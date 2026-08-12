from __future__ import annotations

import logging
import subprocess
from pathlib import Path

from test_framework.cleanup_manager import CleanupManager, terminate_process_group
from test_framework.log_manager import LogManager
from test_framework.logging_utils import log_event, log_exception
from test_framework.network_config import NetworkConfig
from test_framework.port_pool import PortPool
from test_framework.rpc_client import RpcClient
from test_framework.util import SkipTest, find_binary, wait_until

logger = logging.getLogger(__name__)


def find_braidpool_bin(repo_root: Path | None = None) -> Path:
    """Find the braidpool-node binary."""
    return find_binary(
        "braidpool-node",
        "BRAIDPOOL_BIN_PATH",
        ["target/debug/node", "target/release/node", "node"],
        repo_root=repo_root,
    )


class TestNode:
    """Manages a single Braidpool node instance for functional testing."""

    def __init__(
        self,
        index: int,
        datadir: Path,
        config: NetworkConfig,
        ports: PortPool,
        cleanup_manager: CleanupManager,
        log_manager: LogManager,
    ) -> None:
        self.index = index
        self.process: subprocess.Popen | None = None
        self.datadir = Path(datadir) / f"node{index}"
        self.datadir.mkdir(parents=True, exist_ok=True)
        
        self.config = config
        self.rpc_port = ports.allocate("braidpool_rpc", node_id=index)
        self.p2p_port = ports.allocate("braidpool_p2p", node_id=index)
        self.stratum_port = ports.allocate("braidpool_stratum", node_id=index)
        
        self.binary_path = config.braidpool_bin_path or find_braidpool_bin()
        self.rpc = RpcClient("127.0.0.1", self.rpc_port, timeout=config.rpc_timeout)
        
        self.logger = log_manager.logger
        self.cleanup_manager = cleanup_manager
        self.stdout_path, self.stderr_path = log_manager.get_process_log_files(f"node{index}")


    def start(self, extra_args: list[str] | None = None) -> None:
        """Start the braidpool-node process."""
        if self.process is not None and self.process.poll() is None:
            raise RuntimeError(f"Braidpool TestNode {self.index} is already running")

        args = [
            str(self.binary_path),
            f"--network={self.config.network}",
            f"--rpc-bind=127.0.0.1:{self.rpc_port}",
            f"--bind=127.0.0.1:{self.p2p_port}",
            f"--stratum-port={self.stratum_port}",
            f"--datadir={self.datadir}",
        ]
        
        if extra_args:
            args.extend(extra_args)

        log_event(
            self.logger, 
            "braidpool_node_starting", 
            node_id=self.index, 
            rpc_port=self.rpc_port, 
            p2p_port=self.p2p_port,
            stratum_port=self.stratum_port
        )
        
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
            self.cleanup_manager.managed_process(self.process, name=f"node{self.index}")
        except Exception as exc:
            log_exception(self.logger, "braidpool_node_start_failed", exc, node_id=self.index)
            raise
        finally:
            if stdout_file:
                stdout_file.close()
            if stderr_file:
                stderr_file.close()
            
        log_event(self.logger, "braidpool_node_started", node_id=self.index, pid=self.process.pid)

    def wait_for_rpc_connection(self, timeout: float | None = None) -> None:
        """Wait for the Braidpool node RPC to become reachable."""
        timeout = timeout or self.config.startup_timeout_braidpool
        log_event(self.logger, "braidpool_node_wait_rpc", node_id=self.index, timeout=timeout)

        def _check_ready() -> bool:
            # Fast-fail: if the process has already died, don't burn the full timeout.
            if self.process is None or self.process.poll() is not None:
                returncode = self.process.returncode if self.process else "?"
                raise RuntimeError(
                    f"node{self.index} exited (returncode={returncode}) before RPC became ready"
                )
            return self.rpc._try_get_braid_info()

        wait_until(
            _check_ready,
            timeout=timeout,
            message=f"node{self.index} RPC not ready",
        )
        log_event(self.logger, "braidpool_node_rpc_ready", node_id=self.index)

    def stop_node(self, wait: float = 5.0) -> None:
        """Stop the Braidpool node process group."""
        if self.process is None or self.process.poll() is not None:
            log_event(self.logger, "braidpool_node_stop_skipped", level=logging.DEBUG, node_id=self.index)
            # Drop the reference even if already dead so the Popen object can be GC'd.
            self.process = None
            return

        log_event(self.logger, "braidpool_node_stopping", node_id=self.index, pid=self.process.pid)
        terminate_process_group(
            self.process,
            name=f"node{self.index}",
            term_timeout=wait,
            kill_timeout=1.0,
            logger=self.logger,
        )
        log_event(self.logger, "braidpool_node_stopped", node_id=self.index, returncode=self.process.returncode)
        # Set the process reference to none so that the reference with the cleanup manager is the only remaining holder
        # In case of any exceptional ending, if the process is already closed, it will check
        # process.poll() != None and short-circuit cleanly.
        self.process = None

    def wait_until_stopped(self, timeout: float = 10.0) -> None:
        """Wait for the node process to exit naturally."""
        if self.process is None:
            return
        wait_until(
            lambda: self.process.poll() is not None,
            timeout=timeout,
            message=f"node{self.index} stop",
        )

    def is_running(self) -> bool:
        """Check if the Braidpool node process is currently running."""
        return self.process is not None and self.process.poll() is None

    def __getattr__(self, name: str):
        """Delegate unknown attributes to the underlying RpcClient instance."""
        # Guard private attrs and 'rpc' itself to prevent infinite recursion
        # if __getattr__ is triggered before self.rpc is assigned in __init__.
        if name.startswith("_") or name == "rpc":
            raise AttributeError(f"'{self.__class__.__name__}' object has no attribute '{name}'")
        return getattr(self.rpc, name)
