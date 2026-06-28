"""Shared helpers for Braidpool functional tests."""

from __future__ import annotations

import os
import logging
import shutil
import time
from pathlib import Path
from typing import Callable, Iterable, TypeVar

from test_framework.constants import TEST_EXIT_FAILED, TEST_EXIT_PASSED, TEST_EXIT_SKIPPED
from test_framework.logging_utils import log_duration, log_event


logger = logging.getLogger(__name__)

T = TypeVar("T")


class SkipTest(Exception):
    """Raised by a functional test script to report a skipped test."""


def assert_equal(actual: T, expected: T, *more: T) -> None:
    """Assert that all supplied values are equal."""
    values = (actual, expected) + more
    if any(value != actual for value in values[1:]):
        raise AssertionError("not({})".format(" == ".join(repr(value) for value in values)))


def assert_greater_than(actual: int | float, minimum: int | float) -> None:
    """Assert that *actual* is greater than *minimum*."""
    if actual <= minimum:
        raise AssertionError(f"{actual!r} <= {minimum!r}")


def assert_greater_than_or_equal(actual: int | float, minimum: int | float) -> None:
    """Assert that *actual* is greater than or equal to *minimum*."""
    if actual < minimum:
        raise AssertionError(f"{actual!r} < {minimum!r}")

# Generalized wait until function for polling a predicate with timeout and optional message. Majorly used when for waiting for nodes to get ready before using RPCs.
def wait_until(
    predicate: Callable[[], bool],
    *,
    timeout: float = 60.0,
    interval: float = 0.05,
    timeout_factor: float = 1.0,
    message: str | None = None,
) -> None:
    """Poll *predicate* until it returns True or the timeout expires."""
    effective_timeout = timeout * timeout_factor
    started = time.monotonic()
    deadline = time.monotonic() + effective_timeout
    last_error: Exception | None = None

    while time.monotonic() <= deadline:
        try:
            if predicate():
                log_duration(logger, "wait_until_completed", time.monotonic() - started, level=logging.DEBUG)
                return
            last_error = None
        except Exception as exc:
            last_error = exc
        time.sleep(interval)

    detail = message or "wait_until() timed out"
    if last_error is not None:
        detail = f"{detail}; last exception: {last_error!r}"
    log_event(logger, "wait_until_timeout", level=logging.WARNING, timeout_seconds=effective_timeout, detail=detail)
    raise AssertionError(f"{detail} after {effective_timeout:.2f}s")


def find_binary(
    name: str,
    env_var: str,
    relative_paths: Iterable[str | Path],
    *,
    repo_root: Path | None = None,
) -> Path:
    """Find a binary using env var, relative repo paths, then PATH."""
    env_value = os.environ.get(env_var)
    if env_value:
        path = Path(env_value).expanduser()
        if path.exists():
            log_event(logger, "binary_found", level=logging.DEBUG, name=name, source="environment", path=path)
            return path

    root = repo_root or Path.cwd()
    for relative_path in relative_paths:
        path = (root / relative_path).expanduser()
        if path.exists():
            log_event(logger, "binary_found", level=logging.DEBUG, name=name, source="relative_path", path=path)
            return path

    path_from_env = shutil.which(name)
    if path_from_env is not None:
        log_event(logger, "binary_found", level=logging.DEBUG, name=name, source="path", path=path_from_env)
        return Path(path_from_env)

    log_event(logger, "binary_missing", level=logging.WARNING, name=name, env_var=env_var)
    raise SkipTest(f"{name} not found. Set {env_var} or build/install the binary.")
