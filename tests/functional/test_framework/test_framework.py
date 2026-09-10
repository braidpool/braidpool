"""Base lifecycle for executable Braidpool functional test scripts."""

from __future__ import annotations

import argparse
import logging
import pdb
import random
import shutil
import sys
import tempfile
import traceback
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Any, NoReturn

from test_framework.cleanup_manager import CleanupManager
from test_framework.constants import TEST_EXIT_FAILED, TEST_EXIT_PASSED, TEST_EXIT_SKIPPED
from test_framework.log_manager import LogManager
from test_framework.logging_utils import log_event, log_exception
from test_framework.network_config import NetworkConfig
from test_framework.node_manager import NodeManager
from test_framework.port_pool import PortPool, PortSeed
from test_framework.report_manager import ReportManager
from test_framework.util import SkipTest, wait_until as framework_wait_until

if TYPE_CHECKING:
    from test_framework.bitcoin_node import BitcoinNode
    from test_framework.miner_manager import CpuMiner
    from test_framework.test_node import TestNode


class BraidpoolTestMetaClass(type):
    """Protect the framework-owned lifecycle from accidental overrides."""

    def __new__(
        metaclass,
        name: str,
        bases: tuple[type, ...],
        namespace: dict[str, Any],
        **kwargs: Any,
    ) -> BraidpoolTestMetaClass:
        cls = super().__new__(metaclass, name, bases, namespace, **kwargs)
        is_framework_subclass = any(isinstance(base, BraidpoolTestMetaClass) for base in bases)
        if not is_framework_subclass:
            return cls

        forbidden = [method for method in ("__init__", "main") if method in namespace]
        if forbidden:
            methods = ", ".join(forbidden)
            raise TypeError(f"{name} must not override framework lifecycle method(s): {methods}")

        required = [method for method in ("set_test_params", "run_test") if method not in namespace]
        if required:
            methods = ", ".join(required)
            raise TypeError(f"{name} must override required method(s): {methods}")
        return cls


class BraidpoolTestFramework(metaclass=BraidpoolTestMetaClass):
    """Own setup, execution, reporting, and cleanup for one test script.

    Subclasses only define :meth:`set_test_params` and :meth:`run_test`.
    Optional script-specific arguments can be registered through
    :meth:`add_options` without replacing the framework argument parser.
    """

    def __init__(self, test_file: str | Path) -> None:
        self.test_file = Path(test_file).resolve()
        self.test_name = self.test_file.stem

        self.options: argparse.Namespace | None = None
        self.config = NetworkConfig()
        self.timeout_factor = 1.0
        self.tmpdir: Path | None = None

        self.log: logging.Logger = logging.getLogger(f"braidpool.functional.{self.test_name}")
        self.log_manager: LogManager | None = None
        self.cleanup_manager: CleanupManager | None = None
        self.port_pool: PortPool | None = None
        self.node_manager: NodeManager | None = None
        self.report: ReportManager | None = None

        self.bitcoin: BitcoinNode | None = None
        self.nodes: list[TestNode] = []
        self.miners: list[CpuMiner] = []

    def set_test_params(self) -> None:
        """Set ``self.config`` to the network required by the test."""
        raise NotImplementedError

    def run_test(self) -> None:
        """Execute the test scenario after the configured network is ready."""
        raise NotImplementedError

    def add_options(self, parser: argparse.ArgumentParser) -> None:
        """Register optional test-specific command-line arguments."""

    def parse_args(self, argv: Sequence[str] | None = None) -> argparse.Namespace:
        """Parse framework and subclass command-line arguments."""
        parser = argparse.ArgumentParser(description=self.__class__.__doc__)
        parser.add_argument("--tmpdir", type=Path, help="directory for this test's data and reports")
        parser.add_argument("--cachedir", type=Path, help="shared cache directory reserved for future use")
        parser.add_argument("--configfile", type=Path, help="runner configuration file")
        parser.add_argument("--nocleanup", action="store_true", help="preserve the test directory on success")
        parser.add_argument("--loglevel", default=None, help="framework log level")
        parser.add_argument("--tracerpc", action="store_true", help="log RPC request parameters")
        parser.add_argument("--portseed", type=int, default=0, help="deterministic port range seed")
        parser.add_argument("--randomseed", type=int, default=None, help="deterministic random seed")
        parser.add_argument("--timeout-factor", type=float, default=1.0, help="multiply all framework timeouts")
        parser.add_argument("--pdbonfailure", action="store_true", help="open pdb when the test body fails")
        parser.add_argument("--braidpool-bin", type=Path, help="path to the braidpool-node binary")
        parser.add_argument("--bitcoin-bin", type=Path, help="path to the bitcoin-node binary")
        parser.add_argument("--minerd-bin", type=Path, help="path to the minerd binary")
        parser.add_argument("--network", choices=("regtest", "cpunet", "signet"))
        self.add_options(parser)
        self.options = parser.parse_args(argv)

        if self.options.portseed < 0:
            parser.error("--portseed must be greater than or equal to zero")
        if self.options.timeout_factor <= 0:
            parser.error("--timeout-factor must be greater than zero")
        return self.options

    def setup(self) -> None:
        """Create framework managers and start the configured test network."""
        if self.options is None:
            raise RuntimeError("parse_args() must be called before setup()")
        if not isinstance(self.config, NetworkConfig):
            raise TypeError("set_test_params() must assign a NetworkConfig to self.config")

        self._apply_option_overrides()
        self._validate_config()

        self._prepare_test_directory()
        if self.tmpdir is None:
            raise RuntimeError("Test directory was not initialized")

        self.log_manager = LogManager(
            self.tmpdir,
            self.test_name,
            log_level=self.config.log_level,
        )
        self.log = self.log_manager.logger
        log_event(
            self.log,
            "test_setup_started",
            test_name=self.test_name,
            random_seed=self.config.random_seed,
            port_seed=self.options.portseed,
            timeout_factor=self.timeout_factor,
        )

        random.seed(self.config.random_seed)
        PortSeed.n = self.options.portseed
        self.port_pool = PortPool(port_seed=self.options.portseed)
        self.cleanup_manager = CleanupManager(self.log)
        self.cleanup_manager.install_signal_handlers()
        self.node_manager = NodeManager(
            self.config,
            self.log_manager,
            self.cleanup_manager,
            self.port_pool,
        )

        try:
            self.setup_network()
        finally:
            self._refresh_process_handles()

        if self.options.tracerpc:
            self._enable_rpc_tracing()
        log_event(self.log, "test_setup_finished", test_name=self.test_name)

    def setup_network(self) -> None:
        """Start Bitcoin, Braidpool nodes, and miners from ``self.config``."""
        if self.node_manager is None:
            raise RuntimeError("NodeManager is not initialized")
        self.node_manager.setup()

    def shutdown(self, status: int = TEST_EXIT_FAILED) -> int:
        """Stop managed resources, finalize timing, and clean successful runs."""
        options = self.options

        if self.node_manager is not None:
            try:
                self.node_manager.teardown()
            except Exception as exc:
                status = TEST_EXIT_FAILED
                self._log_exception("test_network_teardown_failed", exc)
        if self.cleanup_manager is not None:
            try:
                self.cleanup_manager.run_all()
            except Exception as exc:
                status = TEST_EXIT_FAILED
                self._log_exception("test_cleanup_failed", exc)

        if self.report is not None:
            try:
                self.report.finalize(
                    passed=status == TEST_EXIT_PASSED,
                    skipped=status == TEST_EXIT_SKIPPED,
                )
            except Exception as exc:
                status = TEST_EXIT_FAILED
                self._log_exception("test_report_failed", exc)

        if self.log_manager is not None:
            passed_or_skipped = status in (TEST_EXIT_PASSED, TEST_EXIT_SKIPPED)
            nocleanup = bool(options and options.nocleanup)
            self.log_manager.cleanup(passed=passed_or_skipped, nocleanup=nocleanup)
        elif self.tmpdir is not None:
            preserve = status == TEST_EXIT_FAILED or bool(options and options.nocleanup)
            if not preserve:
                shutil.rmtree(self.tmpdir, ignore_errors=True)
        return status

    def main(self, argv: Sequence[str] | None = None) -> NoReturn:
        """Run the complete test lifecycle and exit with the framework status."""
        status = TEST_EXIT_FAILED
        try:
            self.parse_args(argv)
            # Start the report before subclass code so failures or skips in
            # set_test_params() still produce the same timing artifact.
            self._prepare_test_directory()
            self.set_test_params()
            self.setup()
            self.run_test()
            status = TEST_EXIT_PASSED
            log_event(self.log, "test_passed", test_name=self.test_name)
        except SkipTest as exc:
            status = TEST_EXIT_SKIPPED
            self._log_event("test_skipped", reason=str(exc))
            print(f"{self.test_name}: skipped: {exc}", file=sys.stderr)
        except KeyboardInterrupt as exc:
            status = TEST_EXIT_FAILED
            self._log_exception("test_interrupted", exc)
            print(f"{self.test_name}: interrupted", file=sys.stderr)
        except Exception as exc:
            status = TEST_EXIT_FAILED
            self._log_exception("test_failed", exc)
            traceback.print_exc()
            if self.options is not None and self.options.pdbonfailure:
                pdb.post_mortem(exc.__traceback__)
        finally:
            status = self.shutdown(status)
        raise SystemExit(status)

    def wait_until(
        self,
        predicate: Callable[[], bool],
        *,
        timeout: float = 60.0,
        interval: float = 0.05,
        message: str | None = None,
    ) -> None:
        """Poll a predicate using this test's timeout factor."""
        framework_wait_until(
            predicate,
            timeout=timeout,
            interval=interval,
            timeout_factor=self.timeout_factor,
            message=message,
        )

    def sync_all(self, timeout: float | None = None) -> None:
        """Wait for all Braidpool nodes to agree on their bead count.

        ``timeout`` and the configured default are expressed before applying
        this test's timeout factor.
        """
        if self.node_manager is None:
            raise RuntimeError("The test network has not been set up")
        base_timeout = (
            self.config.bead_propagation_timeout if timeout is None else timeout
        )
        effective_timeout = base_timeout * self.timeout_factor
        self.node_manager.sync_all(timeout=effective_timeout)

    @staticmethod
    def skip_test(reason: str) -> NoReturn:
        """Skip the current test with an explanatory reason."""
        raise SkipTest(reason)

    def _apply_option_overrides(self) -> None:
        if self.options is None:
            raise RuntimeError("Framework options are unavailable")

        self.timeout_factor = self.options.timeout_factor
        if self.options.network is not None:
            self.config.network = self.options.network
        if self.options.randomseed is not None:
            self.config.random_seed = self.options.randomseed
        if self.options.loglevel is not None:
            self.config.log_level = self.options.loglevel
        if self.options.braidpool_bin is not None:
            self.config.braidpool_bin_path = self.options.braidpool_bin
        if self.options.bitcoin_bin is not None:
            self.config.bitcoin_bin_path = self.options.bitcoin_bin
        if self.options.minerd_bin is not None:
            self.config.minerd_bin_path = self.options.minerd_bin

        # sync_all() scales bead_propagation_timeout after choosing between
        # the configured default and a caller-provided timeout.
        for field_name in (
            "startup_timeout_braidpool",
            "startup_timeout_btc",
            "startup_timeout_minerd",
            "rpc_timeout",
            "peer_connection_timeout",
        ):
            current_value = getattr(self.config, field_name)
            setattr(self.config, field_name, current_value * self.timeout_factor)

    def _prepare_test_directory(self) -> None:
        """Create the test directory and begin timing once per lifecycle."""
        if self.tmpdir is not None:
            return
        if self.options is None:
            raise RuntimeError("Framework options are unavailable")

        if self.options.tmpdir is None:
            self.tmpdir = Path(tempfile.mkdtemp(prefix=f"bp_func_test_{self.test_name}_"))
        else:
            self.tmpdir = self.options.tmpdir.expanduser().resolve()
            self.tmpdir.mkdir(parents=True, exist_ok=True)

        run_id = f"{self.test_name}-{self.tmpdir.name}"
        self.report = ReportManager(self.test_name, run_id, self.tmpdir / "reports")

    def _validate_config(self) -> None:
        if self.config.num_braidpool_nodes < 0:
            raise ValueError("num_braidpool_nodes must be greater than or equal to zero")
        if self.config.num_cpu_miners < 0:
            raise ValueError("num_cpu_miners must be greater than or equal to zero")
        if self.config.num_cpu_miners and not self.config.num_braidpool_nodes:
            raise ValueError("num_cpu_miners requires at least one Braidpool node")
        if self.config.network not in ("regtest", "cpunet", "signet"):
            raise ValueError(f"Unsupported network: {self.config.network!r}")

    def _refresh_process_handles(self) -> None:
        if self.node_manager is None:
            return
        self.bitcoin = self.node_manager.bitcoin
        self.nodes = self.node_manager.nodes
        self.miners = self.node_manager.miners

    def _enable_rpc_tracing(self) -> None:
        rpc_clients = []
        if self.bitcoin is not None:
            rpc_clients.append(self.bitcoin.rpc)
        rpc_clients.extend(node.rpc for node in self.nodes)
        for rpc_client in rpc_clients:
            rpc_client.trace = True

    def _log_event(self, event: str, **fields: Any) -> None:
        if self.log_manager is not None:
            log_event(self.log, event, test_name=self.test_name, **fields)

    def _log_exception(self, event: str, exc: BaseException) -> None:
        if self.log_manager is not None:
            log_exception(self.log, event, exc, test_name=self.test_name)
