#!/usr/bin/env python3
"""Verify that a base-class functional test can report a clean skip."""

from __future__ import annotations

from test_framework.network_config import NetworkConfig
from test_framework.test_framework import BraidpoolTestFramework


class FrameworkSkipTest(BraidpoolTestFramework):
    """Exercise exit code 77 and skipped report generation."""

    def set_test_params(self) -> None:
        self.config = NetworkConfig(
            num_braidpool_nodes=0,
            num_cpu_miners=0,
            initial_blocks=0,
        )

    def setup_network(self) -> None:
        """Avoid external binaries; this script only tests skip handling."""

    def run_test(self) -> None:
        self.skip_test("intentional framework self-test skip")


if __name__ == "__main__":
    FrameworkSkipTest(__file__).main()
