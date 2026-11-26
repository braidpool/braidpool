#!/usr/bin/env python3
"""Verify Stratum mining produces a block accepted by Bitcoin Core."""

from test_framework.network_config import NetworkConfig
from test_framework.mock_miner import MockStratumMiner
from test_framework.test_framework import BraidpoolTestFramework


class FeatureMiningBlockAcceptance(BraidpoolTestFramework):

    def set_test_params(self) -> None:
        self.config = NetworkConfig(
            num_braidpool_nodes=2,
            network="regtest",
        )

    def _node_log(self, node) -> str:
        return "\n".join(
            path.read_text(errors="replace")
            for path in (node.stdout_path, node.stderr_path)
            if path.exists()
        )

    def run_test(self) -> None:
        node0, node1 = self.nodes[0], self.nodes[1]

        self.log.info("Test nodes running and RPC is reachable")
        assert node0.is_running() and node1.is_running()
        assert "genesis_beads" in node0.get_braid_info()

        self.log.info("Test miner handshake, work distribution and submission")
        mining_result = MockStratumMiner(
            node0.stratum_port, logger=self.log
        ).mine_one_block(timeout=60.0)
        assert mining_result.job_id, "Miner did not receive mining.notify"
        assert (
            mining_result.difficulty == 0.01
        ), f"Expected share difficulty 0.01, got {mining_result.difficulty}"

        self.log.info("Test and verify the miner found a block accepted by Bitcoin Core")
        assert self.bitcoin is not None, "Bitcoin node was not initialized"
        bitcoin = self.bitcoin
        initial_blocks = self.config.initial_blocks
        assert initial_blocks is not None

        def bitcoin_accepted_mined_block() -> bool:
            blockchain_info = bitcoin.rpc._call("getblockchaininfo")
            accepted_block_seen = "Block ACCEPTED by Bitcoin Core" in self._node_log(node0)
            return (
                accepted_block_seen
                and int(blockchain_info["blocks"]) > initial_blocks
            )

        self.wait_until(
            bitcoin_accepted_mined_block,
            timeout=30.0,
            message="Miner did not produce a block accepted by Bitcoin Core",
        )

        # TODO: Verify Braidpool bead-count growth after an accepted mined block.
        self.log.info("Test P2P")
        node0.wait_for_peers(1, timeout=self.config.peer_connection_timeout)
        node1.wait_for_peers(1, timeout=self.config.peer_connection_timeout)
        self.sync_all()

if __name__ == "__main__":
    FeatureMiningBlockAcceptance(__file__).main()
    