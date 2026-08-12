from __future__ import annotations

import logging

from test_framework.bitcoin_node import BitcoinNode
from test_framework.cleanup_manager import CleanupManager
from test_framework.log_manager import LogManager
from test_framework.logging_utils import log_event
from test_framework.miner_manager import CpuMiner, MinerManager
from test_framework.network_config import NetworkConfig
from test_framework.port_pool import PortPool
from test_framework.test_node import TestNode
from test_framework.util import wait_until

logger = logging.getLogger(__name__)


class NodeManager:
    """Orchestrates the lifecycle and topology of all nodes in a test."""

    def __init__(
        self,
        config: NetworkConfig,
        log_manager: LogManager,
        cleanup_manager: CleanupManager,
        port_pool: PortPool,
    ) -> None:
        self.config = config
        self.log_manager = log_manager
        self.cleanup_manager = cleanup_manager
        self.port_pool = port_pool
        self.logger = log_manager.logger

        self.bitcoin: BitcoinNode | None = None
        self.nodes: list[TestNode] = []
        
        self.miner_manager = MinerManager(config, log_manager, cleanup_manager)

    @property
    def miners(self) -> list[CpuMiner]:
        return self.miner_manager.miners

    def setup(self) -> None:
        """Start all configured nodes and miners in the correct order."""
        log_event(self.logger, "node_manager_setup_started")
        self._start_bitcoin()
        self._start_braidpool_nodes()
        self._start_miners()
        log_event(self.logger, "node_manager_setup_finished")

    def _start_bitcoin(self) -> None:
        """Start Bitcoin Core, wait for readiness, and generate initial blocks."""
        log_event(self.logger, "node_manager_start_bitcoin")
        self.bitcoin = BitcoinNode(
            self.config,
            self.log_manager.tmpdir,
            self.port_pool,
            self.cleanup_manager,
            self.log_manager,
        )
        self.bitcoin.start()          # registers managed_process internally
        self.bitcoin.wait_ready()
        
        if self.config.initial_blocks > 0:
            self.bitcoin.generate_blocks(self.config.initial_blocks)

    def _start_braidpool_nodes(self) -> None:
        """Start Braidpool nodes in a default topology."""
        if self.bitcoin is None:
            raise RuntimeError("Bitcoin must be started before Braidpool nodes")
            
        log_event(self.logger, "node_manager_start_braidpool_nodes", count=self.config.num_braidpool_nodes)
        
        for i in range(self.config.num_braidpool_nodes):
            node = TestNode(
                i,
                self.log_manager.tmpdir,
                self.config,
                self.port_pool,
                self.cleanup_manager,
                self.log_manager,
            )
            
            extra_args = [
                "--bitcoin=127.0.0.1",
                f"--rpcport={self.bitcoin.rpc_port}",
                f"--rpcuser={self.bitcoin.rpc_user}",
                f"--rpcpass={self.bitcoin.rpc_password}",
                # Each test run gets its own IPC socket so concurrent runs
                # don't race on the global /tmp/bitcoin-cpunet.sock default.
                f"--ipc-socket={self.bitcoin.ipc_socket_path}",
            ]
            
            if i > 0:
                extra_args.append(f"--addnode=127.0.0.1:{self.nodes[0].p2p_port}")
                
            node.start(extra_args=extra_args)   # registers managed_process internally
            node.wait_for_rpc_connection()
            
            self.nodes.append(node)

    def _start_miners(self) -> None:
        """Spawn miners attached to the Braidpool nodes."""
        if self.config.num_cpu_miners > 0 and not self.nodes:
            raise RuntimeError("Cannot start miners without Braidpool nodes")
            
        log_event(self.logger, "node_manager_start_miners", count=self.config.num_cpu_miners)
        
        for i in range(self.config.num_cpu_miners):
            node = self.nodes[i % len(self.nodes)]
            self.miner_manager.spawn_miner(node)

    def teardown(self) -> None:
        """Explicitly tear down nodes in reverse order."""
        log_event(self.logger, "node_manager_teardown_started")
        
        self.miner_manager.stop_all()
        
        for node in reversed(self.nodes):
            node.stop_node()
            
        if self.bitcoin:
            self.bitcoin.stop()
            
        log_event(self.logger, "node_manager_teardown_finished")

    def sync_all(self, timeout: float = 60.0) -> None:
        """Wait until all nodes agree on the bead count."""
        if not self.nodes:
            return
            
        log_event(self.logger, "node_manager_sync_all", timeout=timeout)
        
        def all_synced() -> bool:
            counts = [node.get_bead_count() for node in self.nodes]
            return len(set(counts)) == 1
            
        wait_until(
            all_synced,
            timeout=timeout,
            message="Nodes failed to sync bead counts",
        )
        log_event(self.logger, "node_manager_sync_all_finished")
