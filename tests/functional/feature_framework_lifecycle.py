#!/usr/bin/env python3
"""Exercise the base framework lifecycle without requiring external binaries."""

from __future__ import annotations

import argparse
import random
import time
from unittest.mock import Mock

from test_framework.network_config import NetworkConfig
from test_framework.test_framework import BraidpoolTestFramework
from test_framework.util import assert_equal


class SyncAllTimeoutProbe(BraidpoolTestFramework):
    """Expose ``sync_all`` timeout handling without starting a network."""

    def set_test_params(self) -> None:
        self.config = NetworkConfig(bead_propagation_timeout=60.0)

    def run_test(self) -> None:
        """Satisfy the framework subclass contract; this probe is not run."""


class FrameworkLifecycleTest(BraidpoolTestFramework):
    """Validate setup, helpers, reporting, logging, and LIFO cleanup."""

    def add_options(self, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--scenario",
            choices=("pass", "fail", "setup-fail", "cleanup-error", "hang"),
            default="pass",
            help="internal scenario used by the framework self-tests",
        )
        parser.add_argument("--expected-token", default="framework-ready")

    def set_test_params(self) -> None:
        self.config = NetworkConfig(
            num_braidpool_nodes=0,
            num_cpu_miners=0,
            initial_blocks=0,
            random_seed=1729,
        )

    def setup_network(self) -> None:
        """Install deterministic cleanup probes instead of starting binaries."""
        if self.cleanup_manager is None or self.tmpdir is None:
            raise AssertionError("Framework managers were not initialized before setup_network()")

        cleanup_path = self.tmpdir / "cleanup_order.txt"

        def record(name: str, *, fail: bool = False) -> None:
            with cleanup_path.open("a", encoding="utf8") as output:
                output.write(name + "\n")
            if fail:
                raise RuntimeError("intentional cleanup callback failure")

        self.cleanup_manager.register(lambda: record("first"), name="probe:first")
        cleanup_error = self.options.scenario == "cleanup-error"
        middle_name = "failing" if cleanup_error else "middle"
        self.cleanup_manager.register(
            lambda: record(middle_name, fail=cleanup_error),
            name=f"probe:{middle_name}",
        )
        self.cleanup_manager.register(lambda: record("last"), name="probe:last")

        if self.options.scenario == "setup-fail":
            raise RuntimeError("intentional setup failure")

    def run_test(self) -> None:
        if self.options.scenario == "fail":
            raise AssertionError("intentional test failure")
        if self.options.scenario == "hang":
            time.sleep(60)
            return

        if self.tmpdir is None or self.report is None or self.port_pool is None:
            raise AssertionError("Base framework handles were not exposed")
        assert_equal(self.options.expected_token, "framework-ready")
        assert_equal(self.nodes, [])
        assert_equal(self.miners, [])
        assert_equal(self.bitcoin, None)
        assert_equal(self.port_pool.port_seed, self.options.portseed)
        assert_equal(self.report.summary_path.exists(), False)

        expected_random = random.Random(self.config.random_seed).random()
        assert_equal(random.random(), expected_random)

        attempts = 0

        def ready_after_three_attempts() -> bool:
            nonlocal attempts
            attempts += 1
            return attempts == 3

        self.wait_until(ready_after_three_attempts, timeout=1.0, interval=0.001)
        assert_equal(attempts, 3)

        timeout_probe = SyncAllTimeoutProbe(__file__)
        timeout_probe.parse_args(["--timeout-factor=2"])
        timeout_probe.set_test_params()
        timeout_probe._apply_option_overrides()
        assert_equal(timeout_probe.config.bead_propagation_timeout, 60.0)

        timeout_probe.node_manager = Mock()
        sync_all = timeout_probe.node_manager.sync_all

        timeout_probe.sync_all()
        sync_all.assert_called_once_with(timeout=120.0)
        sync_all.reset_mock()

        timeout_probe.sync_all(timeout=60.0)
        sync_all.assert_called_once_with(timeout=120.0)
        sync_all.reset_mock()

        timeout_probe.sync_all(timeout=timeout_probe.config.bead_propagation_timeout)
        sync_all.assert_called_once_with(timeout=120.0)
        self.log.info("Framework lifecycle assertions passed")


if __name__ == "__main__":
    FrameworkLifecycleTest(__file__).main()
