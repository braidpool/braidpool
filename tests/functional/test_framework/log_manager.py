"""Log directory management for Braidpool functional tests."""

from __future__ import annotations

import shutil
from pathlib import Path

from test_framework.constants import FRAMEWORK_LOG_NAME, STDERR_LOG_NAME, STDOUT_LOG_NAME
from test_framework.logging_utils import close_logger, configure_file_logger, log_event, log_exception


class LogManager:
    """Create and clean the log tree for one functional test script."""

    def __init__(
        self,
        tmpdir: Path,
        test_name: str,
        keep_on_success: bool = False,
        *,
        log_level: str | int = "INFO",
    ) -> None:
        self.tmpdir = Path(tmpdir)
        self.test_name = test_name
        self.keep_on_success = keep_on_success
        self.tmpdir.mkdir(parents=True, exist_ok=True)
        self.framework_log = self.tmpdir / FRAMEWORK_LOG_NAME
        self.framework_log.touch(exist_ok=True)
        self._logger_name = f"braidpool.functional.{test_name}"
        self._log_level = log_level
        self.logger = configure_file_logger(
            self._logger_name,
            self.framework_log,
            level=log_level,
        )
        log_event(self.logger, "log_manager_initialized", tmpdir=self.tmpdir, test_name=test_name)

    def subdir(self, name: str) -> Path:
        """Create and return a subdirectory under the test temp directory."""
        path = self.tmpdir / name
        path.mkdir(parents=True, exist_ok=True)
        log_event(self.logger, "log_subdir_ready", level=10, name=name, path=path)
        return path

    def get_process_log_files(self, component: str) -> tuple[Path, Path]:
        """Return stdout/stderr paths for a long-lived subprocess."""
        component_dir = self.subdir(component)
        stdout_path = component_dir / STDOUT_LOG_NAME
        stderr_path = component_dir / STDERR_LOG_NAME
        log_event(
            self.logger,
            "process_log_paths_ready",
            level=10,
            component=component,
            stdout_path=stdout_path,
            stderr_path=stderr_path,
        )
        return stdout_path, stderr_path

    def reports_dir(self) -> Path:
        """Return the reports directory for this test."""
        return self.subdir("reports")

    def cleanup(self, *, passed: bool, nocleanup: bool = False) -> None:
        """Remove the temp directory on successful tests unless preservation is requested."""
        if passed and not nocleanup and not self.keep_on_success:
            try:
                log_event(self.logger, "log_cleanup_started", tmpdir=self.tmpdir)
                close_logger(self.logger)
                shutil.rmtree(self.tmpdir)
            except Exception as exc:
                self.logger = configure_file_logger(self._logger_name, self.framework_log, level=self._log_level)
                log_exception(self.logger, "log_cleanup_failed", exc, tmpdir=self.tmpdir)
        else:
            log_event(
                self.logger,
                "log_cleanup_skipped",
                passed=passed,
                nocleanup=nocleanup,
                keep_on_success=self.keep_on_success,
            )
