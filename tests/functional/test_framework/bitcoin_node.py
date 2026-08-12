from __future__ import annotations

import logging
import subprocess
from pathlib import Path

from test_framework.cleanup_manager import CleanupManager, terminate_process_group
from test_framework.log_manager import LogManager
from test_framework.logging_utils import log_event, log_exception
from test_framework.network_config import NetworkConfig
from test_framework.port_pool import PortPool
from test_framework.rpc_client import RpcClient, RpcError, RpcTransportError, RpcTimeoutError
from test_framework.util import find_binary, wait_until

logger = logging.getLogger(__name__)

def find_bitcoind(repo_root: Path | None = None) -> Path:
    """Find the bitcoin-node binary."""
    return find_binary(
        "bitcoin-node",
        "BITCOIN_NODE_PATH",
        ["../bitcoin/build/bin/bitcoin-node", "bitcoin-node", "target/debug/bitcoin-node"],
        repo_root=repo_root,
    )

class BitcoinNode:
    """Manages a Bitcoin Core (bitcoin-node) instance for testing."""

    def __init__(
        self,
        config: NetworkConfig,
        datadir: Path,
        ports: PortPool,
        cleanup_manager: CleanupManager,
        log_manager: LogManager,
    ) -> None:
        self.config = config
        self.process: subprocess.Popen | None = None
        self.datadir = Path(datadir) / "bitcoin"
        self.datadir.mkdir(parents=True, exist_ok=True)

        self.rpc_port = config.bitcoin_rpc_port or ports.allocate("bitcoin_rpc")
        self.p2p_port = config.bitcoin_p2p_port or ports.allocate("bitcoin_p2p")

        self.rpc_user = "rpcuser"
        self.rpc_password = f"rpcpassword_{ports.port_seed}"

        self.logger = log_manager.logger
        self.cleanup_manager = cleanup_manager

        self.stdout_path, self.stderr_path = log_manager.get_process_log_files("bitcoin")

        self.binary_path = config.bitcoin_bin_path or find_bitcoind()
        self._coinbase_address: str | None = None

        # Per-test IPC socket path so concurrent test runs don't collide on
        # the global default (/tmp/bitcoin-cpunet.sock).
        self.ipc_socket_path: Path = (
            config.bitcoin_ipc_socket
            if config.bitcoin_ipc_socket is not None
            else self.datadir / "bitcoin.sock"
        )

        self.rpc = RpcClient(
            "127.0.0.1",
            self.rpc_port,
            timeout=config.rpc_timeout,
            rpc_user=self.rpc_user,
            rpc_password=self.rpc_password,
            rpc_logger=self.logger,
        )

    def start(self) -> None:
        """Start the bitcoin-node process."""
        if self.process is not None and self.process.poll() is None:
            raise RuntimeError("BitcoinNode is already running")

        if self.config.network not in ("regtest", "signet", "cpunet"):
            raise ValueError(f"Unsupported network: {self.config.network!r}")

        args = [
            str(self.binary_path),
            f"-{self.config.network}",
            f"-datadir={self.datadir}",
            f"-rpcuser={self.rpc_user}",
            f"-rpcpassword={self.rpc_password}",
            f"-rpcport={self.rpc_port}",
            f"-port={self.p2p_port}",
            "-server=1",
            "-fallbackfee=0.0002",
            "-txindex=1",
            "-listen=0",
            "-dnsseed=0",
            "-addresstype=bech32",
            "-deprecatedrpc=create_bdb",
            # Expose the mining IPC socket so the Braidpool node can connect
            # without needing HTTP credentials.  The path is per-test so
            # concurrent test runs never share a socket.
            f"-ipcbind=unix:{self.ipc_socket_path}",
        ]

        log_event(self.logger, "bitcoin_starting", rpc_port=self.rpc_port, p2p_port=self.p2p_port)

        self.stdout_path.parent.mkdir(parents=True, exist_ok=True)
        self.stderr_path.parent.mkdir(parents=True, exist_ok=True)

        stdout_file = None
        stderr_file = None
        try:
            stdout_file = open(self.stdout_path, "ab", buffering=0)
            stderr_file = open(self.stderr_path, "ab", buffering=0)

            self.process = subprocess.Popen(
                args,
                stdout=stdout_file,
                stderr=stderr_file,
                cwd=self.datadir,
                start_new_session=True,
            )
            self.cleanup_manager.managed_process(self.process, name="bitcoin")
        except Exception as exc:
            log_exception(self.logger, "bitcoin_start_failed", exc)
            raise
        finally:
            if stdout_file:
                stdout_file.close()
            if stderr_file:
                stderr_file.close()

        log_event(self.logger, "bitcoin_started", pid=self.process.pid)

    def wait_ready(self, timeout: float | None = None) -> None:
        """Wait for the RPC server to respond to getblockchaininfo."""
        timeout = timeout or self.config.startup_timeout_btc
        log_event(self.logger, "bitcoin_wait_ready", timeout=timeout)

        def _check_ready() -> bool:
            if self.process is None or self.process.poll() is not None:
                returncode = self.process.returncode if self.process else "?"
                raise RuntimeError(
                    f"bitcoin-node exited (returncode={returncode}) before RPC became ready"
                )
            try:
                self.rpc._call("getblockchaininfo")
                return True
            except (RpcTransportError, RpcTimeoutError):
                return False

        wait_until(
            _check_ready,
            timeout=timeout,
            message="Bitcoin RPC not ready",
        )
        log_event(self.logger, "bitcoin_ready")

    def generate_blocks(self, count: int, address: str | None = None) -> list[str]:
        """Mine 'count' blocks to 'address'."""
        if address is None:
            address = self._get_or_create_wallet_address()
        log_event(self.logger, "bitcoin_generate_blocks", count=count, address=address)
        return self.rpc._call("generatetoaddress", [count, address])

    def _get_or_create_wallet_address(self) -> str:
        """Get an address from the default wallet, creating one if needed."""
        if self._coinbase_address:
            return self._coinbase_address

        # Create default wallet if it doesn't exist; tolerate if it already does.
        try:
            self.rpc._call("createwallet", ["default"])
        except RpcError as e:
            if "already exists" not in str(e):
                raise

        self._coinbase_address = self.rpc._call("getnewaddress")
        return self._coinbase_address

    def stop(self) -> None:
        """Stop the bitcoin-node process gracefully, then forcefully if needed."""
        if self.process is None or self.process.poll() is not None:
            log_event(self.logger, "bitcoin_stop_skipped", level=logging.DEBUG)
            # Drop the reference even if already dead so the Popen object can be GC'd.
            self.process = None
            return

        log_event(self.logger, "bitcoin_stopping", pid=self.process.pid)
        try:
            self.rpc._call("stop")
        except Exception as e:
            log_event(self.logger, "bitcoin_stop_rpc_failed", level=logging.WARNING, error=str(e))

        try:
            wait_until(lambda: self.process.poll() is not None, timeout=10.0, message="Bitcoin stop")
            log_event(self.logger, "bitcoin_stopped", returncode=self.process.returncode)
        except AssertionError:
            log_event(self.logger, "bitcoin_stop_timeout", level=logging.WARNING)
            terminate_process_group(
                self.process,
                name="bitcoin",
                term_timeout=2.0,
                kill_timeout=1.0,
                logger=self.logger,
            )
            log_event(self.logger, "bitcoin_force_stopped")
        # Drop reference so CleanupManager's closure is the only remaining holder;
        # it will see process.poll() != None and short-circuit cleanly.
        self.process = None
