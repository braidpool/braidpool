"""JSON-RPC client for Braidpool functional tests."""

from __future__ import annotations

import base64
import json
import logging
import time
import urllib.error
import urllib.request
from itertools import count
from typing import Any, Callable

from test_framework.logging_utils import log_event, log_rpc_call
from test_framework.util import wait_until


logger = logging.getLogger(__name__)

Transport = Callable[[str, bytes, float, str | None], bytes]

_MAX_HTTP_BODY_BYTES = 10 * 1024 * 1024  # 10 MiB cap on HTTP error body reads
_RETRYABLE_OSERRORS = (ConnectionResetError, BrokenPipeError)


class RpcError(Exception):
    """Base exception for JSON-RPC failures."""

    def __init__(self, code: int | None, message: str, data: Any = None) -> None:
        super().__init__(message)
        self.code = code
        self.message = message
        self.data = data


class RpcTransportError(RpcError):
    """Raised when the RPC endpoint cannot be reached."""


class RpcTimeoutError(RpcError):
    """Raised when an RPC call times out."""


class RpcInvalidResponseError(RpcError):
    """Raised when the server returns malformed JSON-RPC data."""


def _default_transport(url: str, payload: bytes, timeout: float, auth_header: str | None = None) -> bytes:
    headers = {"Content-Type": "application/json"}
    if auth_header:
        headers["Authorization"] = auth_header
    request = urllib.request.Request(
        url,
        data=payload,
        headers=headers,
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read(_MAX_HTTP_BODY_BYTES)


class JsonRpcClient:
    """Synchronous JSON-RPC 2.0 client."""

    def __init__(
        self,
        host: str,
        port: int,
        timeout: float = 10.0,
        *,
        rpc_user: str | None = None,
        rpc_password: str | None = None,
        trace: bool = False,
        max_retries: int = 5,
        retry_delay: float = 0.5,
        transport: Transport | None = None,
        rpc_logger: logging.Logger | None = None,
    ) -> None:
        self.url = f"http://{host}:{port}"
        self.timeout = timeout
        self.trace = trace
        self.max_retries = max_retries
        self.retry_delay = retry_delay
        self._transport = transport or _default_transport
        self._ids = count(1)
        self.logger = rpc_logger or logger
        self._auth_header = None
        if rpc_user is not None and rpc_password is not None:
            auth_str = f"{rpc_user}:{rpc_password}"
            encoded_auth = base64.b64encode(auth_str.encode("utf8")).decode("utf8")
            self._auth_header = f"Basic {encoded_auth}"

    def _call(self, method: str, params: Any = None) -> Any:
        started = time.monotonic() # ensures that even if system time changed, actual time is maintained
        request_id = next(self._ids)
        payload_obj = {"jsonrpc": "2.0", "id": request_id, "method": method}
        if params is not None:
            payload_obj["params"] = params
        payload = json.dumps(payload_obj, separators=(",", ":")).encode("utf8")

        safe_params = "<redacted_positional_args>" if isinstance(params, (list, tuple)) else params

        if self.trace:
            log_event(self.logger, "rpc_request", level=logging.DEBUG, method=method, request_id=request_id, params=safe_params)

        try:
            raw = self._send_with_retries(method, payload)
            response = json.loads(raw.decode("utf8"))
            if not isinstance(response, dict):
                raise RpcInvalidResponseError(None, f"JSON-RPC response for {method} is not an object")

            error = response.get("error")
            if error is not None:
                if not isinstance(error, dict):
                    raise RpcInvalidResponseError(None, f"Malformed JSON-RPC error for {method}")
                raise RpcError(error.get("code"), error.get("message", "JSON-RPC error"), error.get("data"))

            if response.get("id") != request_id:
                raise RpcInvalidResponseError(None, f"JSON-RPC response id mismatch for {method}")

            if "result" not in response:
                raise RpcInvalidResponseError(None, f"JSON-RPC response for {method} missing result")
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            error = RpcInvalidResponseError(None, f"Invalid JSON-RPC response for {method}")
            log_rpc_call(
                self.logger,
                method,
                time.monotonic() - started,
                status="error",
                request_id=request_id,
                params=safe_params if self.trace else None,
                error=error.message,
            )
            raise error from exc
        except RpcError as exc:
            log_rpc_call(
                self.logger,
                method,
                time.monotonic() - started,
                status="error",
                request_id=request_id,
                params=safe_params if self.trace else None,
                error=exc.message,
            )
            raise

        log_rpc_call(
            self.logger,
            method,
            time.monotonic() - started,
            status="ok",
            request_id=request_id,
            params=safe_params if self.trace else None,
        )
        return response["result"]

    def _send_with_retries(self, method: str, payload: bytes) -> bytes:
        delay = self.retry_delay
        attempts = self.max_retries + 1
        last_error: BaseException | None = None

        for attempt in range(attempts):
            try:
                return self._transport(self.url, payload, self.timeout, self._auth_header)
            except TimeoutError as exc:
                log_event(self.logger, "rpc_timeout", level=logging.WARNING, method=method, attempt=attempt + 1)
                raise RpcTimeoutError(None, f"RPC {method} timed out") from exc
            except urllib.error.HTTPError as exc:
                if exc.code == 401:
                    raise RpcTransportError(None, f"RPC {method} authentication failed (401 Unauthorized)") from exc
                if exc.code == 500:
                    try:
                        return exc.read(_MAX_HTTP_BODY_BYTES)
                    except Exception:
                        pass
                last_error = exc
                if exc.code != 503 or attempt == attempts - 1:
                    log_event(self.logger, "rpc_http_error", level=logging.WARNING, method=method, attempt=attempt + 1, error=str(exc))
                    raise RpcTransportError(None, f"RPC {method} HTTP error {exc.code}: {exc.reason}") from exc
            except urllib.error.URLError as exc:
                last_error = exc
                if not _is_connection_refused(exc) or attempt == attempts - 1:
                    log_event(self.logger, "rpc_transport_failed", level=logging.WARNING, method=method, attempt=attempt + 1, error=str(exc))
                    raise RpcTransportError(None, f"RPC {method} transport error: {exc}") from exc
            except ConnectionRefusedError as exc:
                last_error = exc
                if attempt == attempts - 1:
                    log_event(self.logger, "rpc_connection_refused", level=logging.WARNING, method=method, attempt=attempt + 1)
                    raise RpcTransportError(None, f"RPC {method} connection refused") from exc
            except OSError as exc:
                if not isinstance(exc, _RETRYABLE_OSERRORS) or attempt == attempts - 1:
                    log_event(self.logger, "rpc_transport_failed", level=logging.WARNING, method=method, attempt=attempt + 1, error=str(exc))
                    raise RpcTransportError(None, f"RPC {method} transport error: {exc}") from exc
                last_error = exc

            log_event(
                self.logger,
                "rpc_retry",
                level=logging.DEBUG,
                method=method,
                attempt=attempt + 1,
                next_delay_seconds=delay,
            )
            if delay > 0:
                time.sleep(delay)
            delay = min(delay * 2, 2.0)

        raise RpcTransportError(None, f"RPC {method} failed: {last_error!r}")

    def __getattr__(self, name: str) -> Callable[..., Any]:
        """Dynamically handle RPC methods not explicitly defined."""
        if name.startswith("_"):
            raise AttributeError(f"'{self.__class__.__name__}' object has no attribute '{name}'")
        
        def rpc_method(*args: Any, **kwargs: Any) -> Any:
            if args and kwargs:
                raise ValueError(f"Cannot pass both positional and keyword arguments to RPC method {name}")
            params = kwargs if kwargs else list(args)
            return self._call(name, params)
            
        return rpc_method


class RpcClient(JsonRpcClient):
    """Braidpool-specific JSON-RPC client."""

    def get_bead(self, bead_hash: str) -> dict:
        return self._call("getbead", [bead_hash])

    def add_bead(self, bead_data: str) -> str:
        return self._call("addbead", [bead_data])

    def get_tips(self) -> list[str]:
        return self._call("gettips")

    def get_bead_count(self) -> int:
        return self._call("getbeadcount")

    def get_cohort_count(self) -> int:
        return self._call("getcohortcount")

    def get_cohort_by_id(self, cohort_id: int) -> list[str]:
        return self._call("getcohortbyid", [cohort_id])

    def get_genesis(self) -> str:
        return self._call("getgenesis")

    def get_braid_info(self) -> dict:
        return self._call("getbraidinfo")

    def get_mining_info(self, **kwargs) -> dict:
        return self._call("getmininginfo", kwargs or {})

    def get_miner_info(self) -> list[str]:
        return self._call("getminerinfo")

    def get_parents(self, bead_hash: str) -> list[str]:
        return self._call("getparents", [bead_hash])

    def get_children(self, bead_hash: str) -> list[str]:
        return self._call("getchildren", [bead_hash])

    def get_highest_work_path_by_count(self, limit: int) -> list[str]:
        return self._call("gethighestworkpathbycount", [limit])

    def get_peer_info(self) -> dict:
        return self._call("getpeerinfo")

    def get_ipc_stats(self) -> dict:
        return self._call("getipcstats")

    def get_node_info(self, bead_hash: str) -> dict:
        return self._call("getnodeinfo", [bead_hash])

    def staged_transactions(self) -> list[dict]:
        return self._call("stagedtransactions")

    def unstage_transactions(self, txid: str) -> bool:
        return self._call("unstagetransactions", [txid])

    def bitcoin_proxy(self, method: str, params: Any = None) -> Any:
        return self._call("bitcoinproxy", [method, params or []])

    def wait_for_ready(self, timeout: float = 30.0) -> None:
        """Poll get_braid_info until the node responds."""
        wait_until(
            lambda: self._try_get_braid_info(),
            timeout=timeout,
            interval=0.5,
            message=f"Node at {self.url} did not become ready",
        )

    def _try_get_braid_info(self) -> bool:
        try:
            self.get_braid_info()
            return True
        except (RpcTransportError, RpcTimeoutError):
            return False

    def wait_for_bead_count(self, minimum: int, timeout: float = 60.0) -> int:
        """Poll get_bead_count until >= minimum. Returns the count."""
        result: list[int] = []
        def check() -> bool:
            count = self.get_bead_count()
            result[:] = [count]
            return count >= minimum
        wait_until(check, timeout=timeout, message=f"Bead count never reached {minimum}")
        return result[0]

    def wait_for_peers(self, minimum: int, timeout: float = 30.0) -> None:
        """Poll get_peer_info until peer count >= minimum."""
        wait_until(
            lambda: len(self.get_peer_info()) >= minimum,
            timeout=timeout,
            message=f"Peer count never reached {minimum}",
        )


def _is_connection_refused(exc: urllib.error.URLError) -> bool:
    reason = getattr(exc, "reason", None)
    return isinstance(reason, ConnectionRefusedError)
