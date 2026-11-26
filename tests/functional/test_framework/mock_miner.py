"""A small Stratum V1 miner for functional tests."""

from __future__ import annotations

import hashlib
import json
import logging
import math
import select
import socket
import time
from collections.abc import Callable, Generator
from collections import deque
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any

from test_framework.logging_utils import log_event


class MockMinerError(RuntimeError):
    """Base exception for failures encountered by the miner."""


class MockMinerAuthorizationError(MockMinerError):
    """The Stratum server rejected miner authorization."""


class MockMinerConnectionError(MockMinerError, ConnectionError):
    """The Stratum connection failed or was closed unexpectedly."""


class MockMinerMiningError(MockMinerError):
    """The miner could not complete its nonce search."""


class MockMinerProtocolError(MockMinerError):
    """The Stratum server sent an invalid or unexpected message."""


class MockMinerRequestError(MockMinerError):
    """The Stratum server returned an error for a request."""


class MockMinerStateError(MockMinerError):
    """The requested operation is invalid for the current miner session."""


class SubmissionRejectedError(MockMinerError):
    """The Stratum server rejected a submitted share or block."""


class MockMinerTimeoutError(MockMinerError, TimeoutError):
    """A Stratum operation or nonce search exceeded its deadline."""


@dataclass(frozen=True, slots=True)
class MockMiningResult:
    """Outcome of one Stratum job mined by :class:`MockStratumMiner`."""

    job_id: str
    difficulty: float
    nonce: str


class MockStratumMiner:
    """Connect to a Braidpool Stratum endpoint and mine one regtest block."""

    def __init__(
        self,
        port: int,
        *,
        host: str = "127.0.0.1",
        worker_name: str = "mock-miner",
        password: str = "x",
        logger: logging.Logger | None = None,
    ) -> None:
        self.host = host
        self.port = port
        self.worker_name = worker_name
        self.password = password
        self.logger = logger
        self._socket: socket.socket | None = None
        self._buffer = bytearray()
        self._pending_messages: deque[dict[str, Any]] = deque()
        self._deadline = 0.0
        self._request_id = 0
        self._extranonce1: str | None = None
        self._extranonce2_size: int | None = None
        self._pending_extranonce: tuple[str, int] | None = None
        self._extranonce2_counter = 0
        self._difficulty: float | None = None
        self._current_job: dict[str, Any] | None = None
        self._clean_job_pending = False

    def _log(self, event: str, *, level: int = logging.INFO, **fields: Any) -> None:
        if self.logger is not None:
            log_event(self.logger, event, level=level, **fields)

    def mine_one_block(self, *, timeout: float = 60.0) -> MockMiningResult:
        """Subscribe, authorize, mine a notified job, and submit its nonce."""
        with self.session(timeout=timeout):
            return self._mine_current_job()

    @contextmanager
    def session(
        self, *, timeout: float = 60.0
    ) -> Generator[MockStratumMiner, None, None]:
        """Keep one authorized Stratum connection open for a test session."""
        self._connect(timeout=timeout)
        try:
            yield self
        finally:
            self.close()

    def _connect(self, *, timeout: float) -> None:
        if timeout <= 0:
            raise ValueError("timeout must be greater than zero")
        if self._socket is not None:
            raise MockMinerStateError("MockStratumMiner is already connected")

        self._log("miner_connecting", host=self.host, port=self.port)
        self._deadline = time.monotonic() + timeout
        while True:
            remaining = self._deadline - time.monotonic()
            if remaining <= 0:
                raise MockMinerTimeoutError(
                    "Timed out connecting to the Stratum server"
                )
            self._buffer.clear()
            self._pending_messages.clear()
            self._request_id = 0
            self._extranonce1 = None
            self._extranonce2_size = None
            self._pending_extranonce = None
            self._extranonce2_counter = 0
            self._difficulty = None
            self._current_job = None
            self._clean_job_pending = False
            try:
                connection = socket.create_connection(
                    (self.host, self.port), timeout=min(remaining, 5.0)
                )
            except OSError as exc:
                if time.monotonic() >= self._deadline:
                    raise MockMinerTimeoutError(
                        "Timed out connecting to the Stratum server"
                    ) from exc
                time.sleep(min(0.1, self._deadline - time.monotonic()))
                continue

            self._socket = connection
            connected = False
            try:
                try:
                    self._extranonce1, self._extranonce2_size = self._subscribe()
                    self._log(
                        "miner_subscribed",
                        extranonce2_size=self._extranonce2_size,
                    )
                except ConnectionError as exc:
                    if time.monotonic() >= self._deadline:
                        raise MockMinerTimeoutError(
                            "Stratum server kept closing connections before subscribe"
                        ) from exc
                    time.sleep(min(0.1, self._deadline - time.monotonic()))
                    continue

                authorization_result = self._request(
                    "mining.authorize", [self.worker_name, self.password]
                )
                if not isinstance(authorization_result, bool) or not authorization_result:
                    self._log(
                        "miner_authorization_rejected",
                        level=logging.WARNING,
                        worker_name=self.worker_name,
                    )
                    raise MockMinerAuthorizationError(
                        "Stratum server rejected miner authorization"
                    )

                self._difficulty, self._current_job = self._wait_for_job()
                self._clean_job_pending = False
                self._log("miner_connected", worker_name=self.worker_name)
                connected = True
                return
            finally:
                if not connected:
                    self.close()

    @property
    def current_job(self) -> dict[str, Any]:
        self._require_socket()
        if self._current_job is None:
            raise MockMinerStateError("No Stratum job has been received")
        return self._current_job

    @property
    def current_difficulty(self) -> float:
        self._require_socket()
        if self._difficulty is None:
            raise MockMinerStateError("No Stratum difficulty has been received")
        return self._difficulty

    def wait_for_next_job(
        self, *, timeout: float = 60.0
    ) -> tuple[float, dict[str, Any]]:
        """Wait for the next job and apply any pending extranonce update."""
        if timeout <= 0:
            raise ValueError("timeout must be greater than zero")
        self._require_socket()
        self._deadline = time.monotonic() + timeout
        self._difficulty, self._current_job = self._wait_for_job()
        self._clean_job_pending = False
        return self._difficulty, self._current_job

    def mine_current_job(self, *, timeout: float = 60.0) -> MockMiningResult:
        """Mine and submit the current job without closing the session."""
        if timeout <= 0:
            raise ValueError("timeout must be greater than zero")
        self._require_socket()
        self._deadline = time.monotonic() + timeout
        return self._mine_current_job()

    def _mine_current_job(self) -> MockMiningResult:
        self._process_available_notifications()
        if self._clean_job_pending:
            raise MockMinerStateError(
                "Current Stratum job was superseded by clean_jobs; "
                "wait for the next job"
            )
        job = self.current_job
        difficulty = self.current_difficulty
        self._log(
            "miner_mining_started",
            job_id=job["job_id"],
            difficulty=difficulty,
        )
        if self._extranonce1 is None or self._extranonce2_size is None:
            raise MockMinerStateError("Stratum session is not subscribed")
        extranonce2_limit = 1 << (8 * self._extranonce2_size)

        def submit_share(nonce: str) -> None:
            try:
                accepted = self._request(
                    "mining.submit",
                    [
                        self.worker_name,
                        job["job_id"],
                        extranonce2.hex(),
                        job["ntime"],
                        nonce,
                    ],
                )
            except SubmissionRejectedError:
                self._log(
                    "miner_share_rejected",
                    level=logging.WARNING,
                    job_id=job["job_id"],
                    nonce=nonce,
                )
                raise
            if accepted is not True:
                self._log(
                    "miner_share_rejected",
                    level=logging.WARNING,
                    job_id=job["job_id"],
                    nonce=nonce,
                )
                raise SubmissionRejectedError(
                    f"Stratum server rejected share for job {job['job_id']}"
                )
            self._log(
                "miner_share_submitted",
                job_id=job["job_id"],
                extranonce2=extranonce2.hex(),
                nonce=nonce,
            )
            self._process_available_notifications()
            if self._clean_job_pending:
                raise MockMinerStateError(
                    "Current Stratum job was superseded by clean_jobs; "
                    "wait for the next job"
                )

        while True:
            if self._extranonce2_counter >= extranonce2_limit:
                raise MockMinerMiningError(
                    "Exhausted extranonce2 values for this session"
                )
            extranonce2 = self._extranonce2_counter.to_bytes(
                self._extranonce2_size, "big"
            )
            self._extranonce2_counter += 1
            nonce = self._find_nonce(
                job,
                self._extranonce1,
                self._extranonce2_size,
                extranonce2=extranonce2,
                on_share=submit_share,
            )
            if nonce is not None:
                break
            self._process_available_notifications()
            if self._clean_job_pending:
                raise MockMinerStateError(
                    "Current Stratum job was superseded by clean_jobs; "
                    "wait for the next job"
                )

        self._process_available_notifications()
        if self._clean_job_pending:
            raise MockMinerStateError(
                "Current Stratum job was superseded by clean_jobs; "
                "wait for the next job"
            )
        try:
            accepted = self._request(
                "mining.submit",
                [
                    self.worker_name,
                    job["job_id"],
                    extranonce2.hex(),
                    job["ntime"],
                    nonce,
                ],
            )
        except SubmissionRejectedError:
            self._log(
                "miner_block_rejected",
                level=logging.WARNING,
                job_id=job["job_id"],
                nonce=nonce,
            )
            raise
        if accepted is not True:
            self._log(
                "miner_block_rejected",
                level=logging.WARNING,
                job_id=job["job_id"],
                nonce=nonce,
            )
            raise SubmissionRejectedError(
                f"Stratum server rejected mined job {job['job_id']}"
            )

        self._log(
            "miner_block_submitted",
            job_id=job["job_id"],
            difficulty=difficulty,
            extranonce2=extranonce2.hex(),
            nonce=nonce,
        )
        return MockMiningResult(
            job_id=job["job_id"],
            difficulty=difficulty,
            nonce=nonce,
        )

    def close(self) -> None:
        """Close the current Stratum session, if one is open."""
        connection = self._socket
        session_established = self._current_job is not None
        self._socket = None
        if connection is not None:
            connection.close()
            if session_established:
                self._log(
                    "miner_session_closed",
                    host=self.host,
                    port=self.port,
                )
        self._buffer.clear()
        self._pending_messages.clear()
        self._extranonce1 = None
        self._extranonce2_size = None
        self._pending_extranonce = None
        self._extranonce2_counter = 0
        self._difficulty = None
        self._current_job = None
        self._clean_job_pending = False

    def _subscribe(self) -> tuple[str, int]:
        result = self._request("mining.subscribe", ["braidpool-mock-miner/1.0"])
        if not isinstance(result, list) or len(result) != 3:
            raise MockMinerProtocolError(
                f"Unexpected mining.subscribe response: {result!r}"
            )
        extranonce1, extranonce2_size = result[1], result[2]
        return self._parse_extranonce(extranonce1, extranonce2_size, "mining.subscribe")

    @staticmethod
    def _parse_extranonce(
        extranonce1: Any, extranonce2_size: Any, source: str
    ) -> tuple[str, int]:
        if not isinstance(extranonce1, str):
            raise MockMinerProtocolError(f"{source} returned an invalid extranonce1")
        try:
            bytes.fromhex(extranonce1)
        except ValueError as exc:
            raise MockMinerProtocolError(
                f"{source} returned a non-hex extranonce1"
            ) from exc
        if type(extranonce2_size) is not int or extranonce2_size <= 0:
            raise MockMinerProtocolError(
                f"{source} returned an invalid extranonce2 size"
            )
        return extranonce1, extranonce2_size

    def _process_set_extranonce_notification(
        self, message: dict[str, Any]
    ) -> bool:
        if message.get("method") != "mining.set_extranonce":
            return False

        params = message.get("params")
        if not isinstance(params, list) or len(params) != 2:
            raise MockMinerProtocolError(
                "Invalid mining.set_extranonce notification"
            )
        extranonce1, extranonce2_size = self._parse_extranonce(
            params[0], params[1], "mining.set_extranonce"
        )
        self._pending_extranonce = (extranonce1, extranonce2_size)
        return True

    def _activate_pending_extranonce(self) -> None:
        if self._pending_extranonce is None:
            return
        extranonce1, extranonce2_size = self._pending_extranonce
        self._pending_extranonce = None
        if (extranonce1, extranonce2_size) != (
            self._extranonce1,
            self._extranonce2_size,
        ):
            self._extranonce2_counter = 0
        self._extranonce1 = extranonce1
        self._extranonce2_size = extranonce2_size

    def _request(self, method: str, params: list[Any]) -> Any:
        self._request_id += 1
        request_id = self._request_id
        self._send({"id": request_id, "method": method, "params": params})
        while True:
            message = self._receive()
            if message.get("id") != request_id:
                if message.get("id") is None:
                    if not self._process_set_extranonce_notification(message):
                        self._queue_notification(message)
                continue
            if message.get("error") is not None:
                error = f"{method} failed with Stratum error: {message['error']!r}"
                if method == "mining.authorize":
                    self._log(
                        "miner_authorization_rejected",
                        level=logging.WARNING,
                        worker_name=self.worker_name,
                    )
                    raise MockMinerAuthorizationError(error)
                if method == "mining.submit":
                    raise SubmissionRejectedError(error)
                raise MockMinerRequestError(error)
            return message.get("result")

    def _wait_for_job(self) -> tuple[float, dict[str, Any]]:
        difficulty = self._difficulty
        job: dict[str, Any] | None = None
        while True:
            if self._pending_messages:
                message = self._pending_messages.popleft()
            else:
                message = self._receive()
                if message.get("id") is None:
                    if self._process_set_extranonce_notification(message):
                        continue
                    self._queue_notification(message)
                    continue
            if message.get("id") is not None:
                continue

            method = message.get("method")
            params = message.get("params")
            if method == "mining.set_difficulty":
                if (
                    not isinstance(params, list)
                    or len(params) != 1
                    or isinstance(params[0], bool)
                    or not isinstance(params[0], (int, float))
                ):
                    raise MockMinerProtocolError(
                        "Invalid mining.set_difficulty notification"
                    )
                try:
                    difficulty = float(params[0])
                except OverflowError as exc:
                    raise MockMinerProtocolError(
                        "Invalid mining.set_difficulty notification"
                    ) from exc
                if not math.isfinite(difficulty) or difficulty <= 0:
                    raise MockMinerProtocolError(
                        "Invalid mining.set_difficulty notification"
                    )
                self._difficulty = difficulty
                self._log("miner_difficulty_received", difficulty=difficulty)
            elif method == "mining.notify":
                if not isinstance(params, list) or len(params) < 9:
                    raise MockMinerProtocolError("Invalid mining.notify job")
                if not isinstance(params[8], bool):
                    raise MockMinerProtocolError(
                        "mining.notify contains an invalid clean_jobs flag"
                    )
                job_id, prevhash, coinbase1, coinbase2, branches, version, bits, ntime = (
                    params[:8]
                )
                if not all(
                    isinstance(value, str)
                    for value in (
                        job_id,
                        prevhash,
                        coinbase1,
                        coinbase2,
                        version,
                        bits,
                        ntime,
                    )
                ):
                    raise MockMinerProtocolError(
                        "mining.notify contains invalid string fields"
                    )
                if not isinstance(branches, list) or not all(
                    isinstance(branch, str) for branch in branches
                ):
                    raise MockMinerProtocolError(
                        "mining.notify contains an invalid merkle path"
                    )
                self._activate_pending_extranonce()
                job = {
                    "job_id": job_id,
                    "prevhash": prevhash,
                    "coinbase1": coinbase1,
                    "coinbase2": coinbase2,
                    "merkle_branches": branches,
                    "version": version,
                    "bits": bits,
                    "ntime": ntime,
                }
            if difficulty is not None and job is not None:
                self._log(
                    "miner_job_received",
                    job_id=job["job_id"],
                    difficulty=difficulty,
                    bits=job["bits"],
                )
                return difficulty, job

    def _find_nonce(
        self,
        job: dict[str, Any],
        extranonce1: str,
        extranonce2_size: int,
        *,
        extranonce2: bytes | None = None,
        on_share: Callable[[str], None] | None = None,
    ) -> str | None:
        try:
            extranonce2 = extranonce2 if extranonce2 is not None else bytes(extranonce2_size)
            if len(extranonce2) != extranonce2_size:
                raise ValueError("extranonce2 has an invalid length")
            coinbase = bytes.fromhex(
                job["coinbase1"]
                + extranonce1
                + extranonce2.hex()
                + job["coinbase2"]
            )
            merkle_root = self._double_sha256(coinbase)
            for branch in job["merkle_branches"]:
                branch_bytes = bytes.fromhex(branch)
                if len(branch_bytes) != 32:
                    raise ValueError("Merkle branch entries must be 32 bytes")
                merkle_root = self._double_sha256(merkle_root + branch_bytes)

            version = self._decode_hex(job["version"], "version", 4)[::-1]
            prevhash_wire = self._decode_hex(job["prevhash"], "prevhash", 32)
            prevhash = b"".join(
                prevhash_wire[offset : offset + 4][::-1]
                for offset in range(0, len(prevhash_wire), 4)
            )
            ntime = self._decode_hex(job["ntime"], "ntime", 4)[::-1]
            bits = self._decode_hex(job["bits"], "bits", 4)
            block_target = self._target_from_compact(int.from_bytes(bits, "big"))
            share_target = (
                self._target_from_difficulty(self._difficulty)
                if self._difficulty is not None
                else None
            )
        except (TypeError, ValueError) as exc:
            raise MockMinerProtocolError(f"Invalid Stratum job: {exc}") from exc

        header_prefix = version + prevhash + merkle_root + ntime + bits[::-1]
        if len(header_prefix) != 76:
            raise MockMinerProtocolError(
                "Constructed block header has an invalid length"
            )

        for nonce_value in range(1 << 32):
            if nonce_value & 0xFFF == 0 and time.monotonic() >= self._deadline:
                raise MockMinerTimeoutError(
                    "Timed out while searching for a valid nonce"
                )
            nonce_bytes = nonce_value.to_bytes(4, "little")
            block_hash = self._double_sha256(header_prefix + nonce_bytes)
            hash_value = int.from_bytes(block_hash, "little")
            nonce = nonce_value.to_bytes(4, "big").hex()
            if hash_value <= block_target:
                return nonce
            if share_target is not None and hash_value <= share_target:
                if on_share is None:
                    raise MockMinerMiningError(
                        "Found a share-only solution without a submission handler"
                    )
                on_share(nonce)
        return None

    @staticmethod
    def _decode_hex(value: str, name: str, expected_bytes: int) -> bytes:
        decoded = bytes.fromhex(value)
        if len(decoded) != expected_bytes:
            raise ValueError(f"{name} must be {expected_bytes} bytes")
        return decoded

    @staticmethod
    def _target_from_compact(compact: int) -> int:
        exponent = compact >> 24
        mantissa = compact & 0x007FFFFF
        if compact & 0x00800000 or mantissa == 0:
            raise ValueError("compact target is negative or zero")
        if exponent <= 3:
            target = mantissa >> (8 * (3 - exponent))
        else:
            target = mantissa << (8 * (exponent - 3))
        if target <= 0 or target >= 1 << 256:
            raise ValueError("compact target is out of range")
        return target

    @classmethod
    def _target_from_difficulty(cls, difficulty: float) -> int:
        if not math.isfinite(difficulty) or difficulty <= 0:
            raise ValueError("difficulty must be finite and greater than zero")
        numerator, denominator = difficulty.as_integer_ratio()
        diff1_target = cls._target_from_compact(0x1D00FFFF)
        return min(
            (diff1_target * denominator) // numerator,
            (1 << 256) - 1,
        )

    def _send(self, message: dict[str, Any]) -> None:
        connection = self._require_socket()
        payload = json.dumps(message, separators=(",", ":")).encode("utf-8") + b"\n"
        try:
            connection.sendall(payload)
        except TimeoutError as exc:
            raise MockMinerTimeoutError(
                f"Timed out sending Stratum request: {exc}"
            ) from exc
        except OSError as exc:
            raise MockMinerConnectionError(
                f"Failed to send Stratum request: {exc}"
            ) from exc

    def _receive(self) -> dict[str, Any]:
        connection = self._require_socket()
        while True:
            message = self._pop_buffered_message()
            if message is not None:
                return message
            remaining = self._deadline - time.monotonic()
            if remaining <= 0:
                raise MockMinerTimeoutError("Timed out waiting for a Stratum message")
            try:
                readable, _, _ = select.select([connection], [], [], remaining)
            except OSError as exc:
                raise MockMinerConnectionError(
                    f"Failed waiting for a Stratum message: {exc}"
                ) from exc
            if not readable:
                raise MockMinerTimeoutError("Timed out waiting for a Stratum message")
            try:
                chunk = connection.recv(4096)
            except TimeoutError as exc:
                raise MockMinerTimeoutError(
                    f"Timed out receiving a Stratum message: {exc}"
                ) from exc
            except OSError as exc:
                raise MockMinerConnectionError(
                    f"Failed receiving a Stratum message: {exc}"
                ) from exc
            if not chunk:
                raise MockMinerConnectionError(
                    "Stratum server closed the connection"
                )
            self._buffer.extend(chunk)
            if len(self._buffer) > 1024 * 1024:
                raise MockMinerProtocolError("Stratum message exceeded 1 MiB")

    def _process_available_notifications(self) -> None:
        pending_count = len(self._pending_messages)
        for _ in range(pending_count):
            message = self._pending_messages.popleft()
            if not self._process_set_extranonce_notification(message):
                self._pending_messages.append(message)

        connection = self._require_socket()
        while True:
            message = self._pop_buffered_message()
            if message is None:
                try:
                    readable, _, _ = select.select([connection], [], [], 0)
                except OSError as exc:
                    raise MockMinerConnectionError(
                        f"Failed waiting for a Stratum notification: {exc}"
                    ) from exc
                if not readable:
                    return
                try:
                    chunk = connection.recv(4096)
                except TimeoutError as exc:
                    raise MockMinerTimeoutError(
                        f"Timed out receiving a Stratum notification: {exc}"
                    ) from exc
                except OSError as exc:
                    raise MockMinerConnectionError(
                        f"Failed receiving a Stratum notification: {exc}"
                    ) from exc
                if not chunk:
                    raise MockMinerConnectionError(
                        "Stratum server closed the connection"
                    )
                self._buffer.extend(chunk)
                if len(self._buffer) > 1024 * 1024:
                    raise MockMinerProtocolError("Stratum message exceeded 1 MiB")
                continue
            if message.get("id") is not None:
                raise MockMinerProtocolError(
                    "Received an unsolicited Stratum response without a pending request"
                )
            if not self._process_set_extranonce_notification(message):
                self._queue_notification(message)

    def _queue_notification(self, message: dict[str, Any]) -> None:
        if message.get("method") == "mining.notify":
            params = message.get("params")
            if isinstance(params, list) and len(params) >= 9:
                if not isinstance(params[8], bool):
                    raise MockMinerProtocolError(
                        "mining.notify contains an invalid clean_jobs flag"
                    )
                if params[8]:
                    self._pending_messages = deque(
                        pending
                        for pending in self._pending_messages
                        if pending.get("method") != "mining.notify"
                    )
                    self._clean_job_pending = True
        self._pending_messages.append(message)

    def _pop_buffered_message(self) -> dict[str, Any] | None:
        line_end = self._buffer.find(b"\n")
        if line_end == -1:
            return None
        line = bytes(self._buffer[:line_end])
        del self._buffer[: line_end + 1]
        try:
            message = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise MockMinerProtocolError(
                f"Invalid JSON from Stratum server: {line!r}"
            ) from exc
        if not isinstance(message, dict):
            raise MockMinerProtocolError(
                "Stratum server message must be a JSON object"
            )
        return message

    def _require_socket(self) -> socket.socket:
        if self._socket is None:
            raise MockMinerStateError("MockStratumMiner is not connected")
        return self._socket

    @staticmethod
    def _double_sha256(data: bytes) -> bytes:
        return hashlib.sha256(hashlib.sha256(data).digest()).digest()
