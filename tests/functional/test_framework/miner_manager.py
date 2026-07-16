"""CpuMiner process helpers for Braidpool functional tests."""

from __future__ import annotations

import logging
import re
import subprocess
from pathlib import Path
from typing import Any, Callable, Protocol

from test_framework.constants import STDERR_LOG_NAME, STDOUT_LOG_NAME
from test_framework.log_manager import LogManager
from test_framework.logging_utils import log_event, log_exception
from test_framework.network_config import NetworkConfig
from test_framework.cleanup_manager import terminate_process_group
from test_framework.util import SkipTest, find_binary


class _Registerable(Protocol):
    def register(self, fn: Callable[[], None]) -> None: ...


class StratumNode(Protocol):
    @property
    def stratum_port(self) -> int: ...


ACCEPTED_SHARE_RE = re.compile(r"\b(accepted|share accepted|accepted share)\b", re.IGNORECASE)
logger = logging.getLogger(__name__)


class CpuMiner:
    """Wrap a single cpuminer process."""

    def __init__(
        self,
        stratum_port: int,
        run_dir: Path,
        *,
        minerd_path: str | Path = "minerd",
        algorithm: str = "sha256d",
        miner_id: int = 0,
        miner_logger: logging.Logger | None = None,
    ) -> None:
        self.stratum_port = stratum_port
        self.run_dir = Path(run_dir)
        self.minerd_path = Path(minerd_path)
        self.algorithm = algorithm
        self.miner_id = miner_id
        self.process: subprocess.Popen | None = None
        self.logger = miner_logger or logger
        self.stdout_path = self.run_dir / STDOUT_LOG_NAME
        self.stderr_path = self.run_dir / STDERR_LOG_NAME
        self.run_dir.mkdir(parents=True, exist_ok=True)

    def __del__(self) -> None:
        if self.process is not None and self.process.poll() is None:
            try:
                self.process.kill()
            except OSError:
                pass

    def start(self, extra_args: list[str] | None = None) -> None:
        """Start minerd with stdout/stderr redirected to files."""
        if self.is_alive():
            raise RuntimeError(f"CpuMiner {self.miner_id} is already running")
        DEFAULT_MINERD_FLAGS = ["-q", "-D", "-P"]
        args = [
            str(self.minerd_path),
            "-a",
            self.algorithm,
            "-o",
            f"stratum+tcp://127.0.0.1:{self.stratum_port}",
            *DEFAULT_MINERD_FLAGS,
        ]
        if extra_args:
            args.extend(extra_args)

        log_event(
            self.logger,
            "miner_starting",
            miner_id=self.miner_id,
            stratum_port=self.stratum_port,
            algorithm=self.algorithm,
            stdout_path=self.stdout_path,
            stderr_path=self.stderr_path,
        )
        stdout_file = open(self.stdout_path, "ab", buffering=0)
        stderr_file = open(self.stderr_path, "ab", buffering=0)
        try:
            try:
                self.process = subprocess.Popen(
                    args,
                    stdout=stdout_file,
                    stderr=stderr_file,
                    cwd=self.run_dir,
                    start_new_session=True,
                )
            except Exception as exc:
                log_exception(self.logger, "miner_start_failed", exc, miner_id=self.miner_id)
                raise
        finally:
            stdout_file.close()
            stderr_file.close()
        log_event(self.logger, "miner_started", miner_id=self.miner_id, pid=self.process.pid)

    def stop(self, *, term_timeout: float = 2.0, kill_timeout: float = 1.0) -> None:
        """Stop the miner process group. Safe to call repeatedly."""
        process = self.process
        if process is None or process.poll() is not None:
            log_event(self.logger, "miner_stop_skipped", level=logging.DEBUG, miner_id=self.miner_id)
            return
        log_event(self.logger, "miner_stopping", miner_id=self.miner_id, pid=process.pid)
        terminate_process_group(
            process,
            name=f"miner{self.miner_id}",
            term_timeout=term_timeout,
            kill_timeout=kill_timeout,
            logger=self.logger,
        )
        log_event(self.logger, "miner_stopped", miner_id=self.miner_id, returncode=process.returncode)

    def is_alive(self) -> bool:
        return self.process is not None and self.process.poll() is None

    def shares_submitted(self) -> int:
        """Parse miner logs and return the number of accepted shares."""
        count = 0
        for path in (self.stdout_path, self.stderr_path):
            if not path.exists():
                continue
            with path.open("r", encoding="utf8", errors="replace") as log_file:
                for line in log_file:
                    if ACCEPTED_SHARE_RE.search(line):
                        count += 1
        log_event(self.logger, "miner_share_count", level=logging.DEBUG, miner_id=self.miner_id, accepted_shares=count)
        return count


class MinerManager:
    """Factory and lifecycle manager for CpuMiner instances."""

    def __init__(
        self,
        config: NetworkConfig,
        log_manager: LogManager,
        cleanup: _Registerable | None = None,  # when the test case runs, it registers the cleanup maanger with the test framework, so we can register miner stop functions to be called on test cleanup
    ) -> None:
        self.config = config
        self.log_manager = log_manager
        self.cleanup = cleanup
        self.miners: list[CpuMiner] = []
        self.logger = log_manager.logger

    def spawn_miner(self, node: StratumNode) -> CpuMiner:
        """Create and start a miner attached to *node*'s stratum port."""
        stratum_port = node.stratum_port
        if stratum_port is None:
            raise TypeError(
                f"spawn_miner: node {node!r} has no 'stratum_port' attribute. "
                "Pass a BraidpoolNode instance."
            )
        miner_id = len(self.miners)
        minerd_path = self._resolve_minerd_path()
        log_event(self.logger, "miner_spawn_requested", miner_id=miner_id, stratum_port=stratum_port)
        run_dir = self.log_manager.subdir(f"miner{miner_id}")
        miner = CpuMiner(
            stratum_port,
            run_dir,
            minerd_path=minerd_path,
            miner_id=miner_id,
            miner_logger=self.logger,
        )
        miner.start()
        self.miners.append(miner)
        if self.cleanup is not None:
            self.cleanup.register(miner.stop)
        return miner

    def stop_all(self) -> None:
        log_event(self.logger, "miner_stop_all_started", miner_count=len(self.miners))
        for miner in reversed(self.miners):
            miner.stop()
        log_event(self.logger, "miner_stop_all_finished", miner_count=len(self.miners))

    def _resolve_minerd_path(self) -> Path:
        if self.config.minerd_bin_path is not None:
            path = Path(self.config.minerd_bin_path)
            if path.exists():
                return path
        return find_minerd()


def find_minerd(repo_root: Path | None = None) -> Path:
    """Find the minerd binary using the standard functional-test search order."""
    return find_binary(
        "minerd",
        "MINERD_PATH",
        ["node/src/cpuminer/minerd"],
        repo_root=repo_root,
    )
