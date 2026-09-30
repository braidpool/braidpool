"""Timing reports for Braidpool functional test scripts."""

from __future__ import annotations

import json
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


class ReportManager:
    """
    Record the wall-clock start, end, and total runtime of one test script.
    """

    SUMMARY_FILE_NAME = "summary.json"

    def __init__(self, test_name: str, run_id: str, reports_dir: Path) -> None:
        if not test_name:
            raise ValueError("test_name must not be empty")
        if not run_id:
            raise ValueError("run_id must not be empty")

        self.test_name = test_name
        self.run_id = run_id
        self.reports_dir = Path(reports_dir)
        self.reports_dir.mkdir(parents=True, exist_ok=True)

        self.start_time = datetime.now(tz=timezone.utc)
        self.end_time: datetime | None = None
        self.total_time_seconds: float | None = None
        self._started_monotonic = time.monotonic()
        self._finalized = False
        self._finalize_lock = threading.Lock()

    @property
    def summary_path(self) -> Path:
        """Return the path of this test's JSON summary."""
        return self.reports_dir / self.SUMMARY_FILE_NAME

    def finalize(self, passed: bool, skipped: bool = False) -> None:
        """Finish timing and write ``summary.json`` exactly once.

        Args:
            passed: Whether the test completed successfully.
            skipped: Whether the test was skipped.  A skipped status takes
                precedence over ``passed`` when constructing the summary.
        """
        with self._finalize_lock:
            if self._finalized:
                return

            self.end_time = datetime.now(tz=timezone.utc)
            self.total_time_seconds = max(0.0, time.monotonic() - self._started_monotonic)
            status = "skipped" if skipped else "passed" if passed else "failed"
            payload: dict[str, Any] = {
                "test_name": self.test_name,
                "run_id": self.run_id,
                "status": status,
                "start_time": self.start_time.isoformat(timespec="milliseconds"),
                "end_time": self.end_time.isoformat(timespec="milliseconds"),
                "total_time_seconds": round(self.total_time_seconds, 6),
            }

            temporary_path = self.summary_path.with_suffix(".json.tmp")
            temporary_path.write_text(
                json.dumps(payload, indent=2, sort_keys=True) + "\n",
                encoding="utf8",
            )
            temporary_path.replace(self.summary_path)
            self._finalized = True
