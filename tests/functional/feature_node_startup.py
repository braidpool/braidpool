#!/usr/bin/env python3
"""Verify that two Braidpool nodes start, expose RPC, and synchronize."""

import argparse
import sys
import tempfile
from pathlib import Path

from test_framework.cleanup_manager import CleanupManager
from test_framework.constants import TEST_EXIT_FAILED, TEST_EXIT_PASSED, TEST_EXIT_SKIPPED
from test_framework.log_manager import LogManager
from test_framework.logging_utils import configure_stream_logger, log_event
from test_framework.network_config import NetworkConfig
from test_framework.node_manager import NodeManager
from test_framework.port_pool import PortPool
from test_framework.util import SkipTest


def run_test(node_manager: NodeManager) -> None:
    assert node_manager.bitcoin is not None

    # 1. RPC reachable
    info = node_manager.nodes[0].rpc.get_braid_info()
    assert "bead_count" in info

    # 2. Node is alive
    assert node_manager.nodes[0].is_running()

    # 3. Bitcoin reachable
    btc_info = node_manager.bitcoin.rpc._call("getblockchaininfo")
    assert btc_info["chain"] == node_manager.config.network

    # 4. Initial blocks mined
    assert btc_info["blocks"] >= node_manager.config.initial_blocks

    # 5. Bead count is > 0
    assert node_manager.nodes[0].rpc.get_bead_count() > 0

    # 6. Tips list is a list
    tips = node_manager.nodes[0].rpc.get_tips()
    assert isinstance(tips, list)

    # 7. Verify both nodes are alive and synced
    assert len(node_manager.nodes) == 2, "Expected exactly 2 Braidpool nodes to be running"
    assert node_manager.nodes[1].is_running()
    node_manager.sync_all(timeout=30.0)

    # 8. Verify miner info from RPC returns empty list since no miners are connected
    miner_info = node_manager.nodes[0].rpc.get_miner_info()
    assert isinstance(miner_info, list)
    assert len(miner_info) == 0

    log_event(node_manager.logger, "test_assertions_passed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tmpdir", type=Path)
    parser.add_argument("--portseed", type=int, default=0)
    parser.add_argument("--nocleanup", action="store_true")
    parser.add_argument("--braidpool-bin", type=Path)
    parser.add_argument("--bitcoin-bin", type=Path)
    # The runner passes through unhandled arguments, so we can ignore any we don't need
    args, _ = parser.parse_known_args()
    
    tmpdir = args.tmpdir or Path(tempfile.mkdtemp(prefix="bp_func_test_"))
    
    configure_stream_logger(None, level="WARNING")
    
    cleanup = CleanupManager()
    cleanup.install_signal_handlers()  # must be called explicitly; constructor is side-effect-free
    log_manager = LogManager(tmpdir, "feature_node_startup", keep_on_success=args.nocleanup)
    port_pool = PortPool(port_seed=args.portseed)
    
    config = NetworkConfig(num_braidpool_nodes=2, num_cpu_miners=0)
    if args.braidpool_bin:
        config.braidpool_bin_path = args.braidpool_bin
    if args.bitcoin_bin:
        config.bitcoin_bin_path = args.bitcoin_bin
        
    node_manager = NodeManager(config, log_manager, cleanup, port_pool)
    passed = False
    skipped = False
    
    try:
        node_manager.setup()
        
        # Verify Datadirs are created
        assert (tmpdir / "node0").exists(), "Node 0 datadir missing"
        assert (tmpdir / "node1").exists(), "Node 1 datadir missing"
        assert (tmpdir / "bitcoin").exists(), "Bitcoin datadir missing"
        
        run_test(node_manager)
        
        log_event(log_manager.logger, "test_success")
        passed = True
        return TEST_EXIT_PASSED
        
    except SkipTest as exc:
        skipped = True
        log_event(log_manager.logger, "test_skipped", reason=str(exc))
        return TEST_EXIT_SKIPPED
    except Exception as exc:
        log_event(log_manager.logger, "test_failed", error=str(exc))
        return TEST_EXIT_FAILED
    finally:
        node_manager.teardown()
        cleanup.run_all()
        # Skipped tests also clean up — only failures retain the tmpdir.
        log_manager.cleanup(passed=passed or skipped, nocleanup=args.nocleanup)


if __name__ == "__main__":
    sys.exit(main())
