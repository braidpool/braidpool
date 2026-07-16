"""LIFO cleanup orchestration for Braidpool functional tests."""

from __future__ import annotations

import atexit
import logging
import os
import signal
import subprocess
import threading
from collections.abc import Callable
from types import FrameType
import time

from test_framework.logging_utils import log_event, log_exception, log_duration


_LOGGER = logging.getLogger(__name__)


class CleanupManager:
    """Register and run cleanup callbacks for a functional test process.

    Instances install ``atexit``, ``SIGTERM``, and ``SIGINT`` hooks during
    initialization. Construct this class from the main thread; CPython only
    allows signal handlers to be installed there.
    """

    def __init__(
        self,
        logger: logging.Logger | None = None,
    ) -> None:
        self._logger = logger or _LOGGER
        self._stack: list[tuple[str, Callable[[], None]]] = []
        self._lock = threading.RLock()
        self._ran = False
        self._previous_handlers: dict[int, signal.Handlers] = {}

    # The cleanup manager is a registrable that is attached to different modules
    # later when running the test suite such as miner_manager. This allows us to
    # register different callback functions in a LIFO stack.
    def register(self, fn: Callable[[], None], *, name: str | None = None) -> None:
        """Push a zero-argument cleanup callback onto the LIFO stack."""
        callback_name = name or _callable_name(fn)
        with self._lock:
            if self._ran:
                log_event(
                    self._logger,
                    "cleanup_register_after_run",
                    level=logging.WARNING,
                    name=callback_name,
                )
                return
            self._stack.append((callback_name, fn))
        log_event(
            self._logger,
            "cleanup_callback_registered",
            level=logging.DEBUG,
            name=callback_name,
        )

    def run_all(self) -> None:
        """Execute all registered callbacks in LIFO order exactly once."""
        with self._lock:
            if self._ran:
                return
            self._ran = True
            stack = list(self._stack)

        for name, fn in reversed(stack):
            try:
                log_event(self._logger, "cleanup_callback_running", name=name)
                fn()
                log_event(self._logger, "cleanup_callback_done", name=name)
            except Exception as exc:
                log_exception(self._logger, "cleanup_callback_failed", exc, name=name)

        # restore previous signal handlers so that subsequent
        # code is not left with stale references to this now-finished CleanupManager.
        for signum, handler in self._previous_handlers.items():
            try:
                signal.signal(signum, handler)
            except (OSError, ValueError):
                # Not the main thread, or signal already changed — skip.
                pass
        self._previous_handlers.clear()
        atexit.unregister(self.run_all)

    def managed_process(
        self,
        process: subprocess.Popen,
        name: str,
        *,
        term_timeout: float = 3.0,
        kill_timeout: float = 1.0,
    ) -> None:
        """Register a callback that terminates a subprocess group on cleanup."""

        def _stop() -> None:
            terminate_process_group(
                process,
                name=name,
                term_timeout=term_timeout,
                kill_timeout=kill_timeout,
                logger=self._logger,
            )

        self.register(_stop, name=f"process:{name}")

    # Install atexit and signal handlers when the CleanupManager is initialized.
    # Sets up a signal chaining mechanism so that when the test process is
    # terminated due to signals it can gracefully exit after running all the
    # cleanup callbacks.
    def install_signal_handlers(self) -> None:
        atexit.register(self.run_all)
        for signum in (signal.SIGTERM, signal.SIGINT):
            self._previous_handlers[signum] = signal.getsignal(signum)
            signal.signal(signum, self._signal_handler)

    def _signal_handler(self, signum: int, frame: FrameType | None) -> None:
        log_event(self._logger, "cleanup_signal_received", signal=signum)
        self.run_all()
        self._delegate_signal(signum, frame)

    def _delegate_signal(self, signum: int, frame: FrameType | None) -> None:
        previous = self._previous_handlers.get(signum, signal.SIG_DFL)
        if previous == signal.SIG_IGN:
            return
        if callable(previous):
            previous(signum, frame)
            return
        # No custom prior handler — restore default and re-raise so the OS
        # records the correct exit status (e.g. 128 + signum).
        log_event(
            self._logger,
            "cleanup_re_raising_signal",
            level=logging.WARNING,
            signal=signum,
            message=f"Re-raising signal {signum} with SIG_DFL; process will now terminate",
        )
        signal.signal(signum, signal.SIG_DFL)
        os.kill(os.getpid(), signum)


def _callable_name(fn: Callable[[], None]) -> str:
    return getattr(fn, "__qualname__", getattr(fn, "__name__", repr(fn)))


def terminate_process_group(
    process: subprocess.Popen,
    *,
    name: str,
    term_timeout: float,
    kill_timeout: float,
    logger: logging.Logger | None = None,
) -> None:
    """Terminate *process* and its process group with SIGTERM, then SIGKILL.

    The process **must** have been started with ``start_new_session=True``
    so that its PGID differs from the caller's.  An assertion guards
    against accidental self-kill.
    """
    process_logger = logger or _LOGGER
    if process.poll() is not None:
        log_event(
            process_logger,
            "process_stop_skipped",
            level=logging.DEBUG,
            name=name,
            pid=process.pid,
            returncode=process.returncode,
        )
        return

    try:
        pgid = os.getpgid(process.pid)
    except OSError:
        log_event(
            process_logger,
            "process_group_missing",
            level=logging.DEBUG,
            name=name,
            pid=process.pid,
        )
        return

    # re-poll immediately after getpgid() to narrow the TOCTOU
    # window. Between poll() and getpgid() the process could have exited and
    # its PID recycled to an unrelated process.
    if process.poll() is not None:
        log_event(
            process_logger,
            "process_exited_before_signal",
            level=logging.DEBUG,
            name=name,
            pid=process.pid,
        )
        return

    # Guard: never kill our own process group.
    if pgid == os.getpgid(0):
        log_event(
            process_logger,
            "process_group_is_self",
            level=logging.ERROR,
            name=name,
            pid=process.pid,
            pgid=pgid,
        )
        # Fall back to killing just the single process.
        try:
            process.terminate()
            process.wait(timeout=term_timeout)
        except (OSError, subprocess.TimeoutExpired):
            try:
                process.kill()
                process.wait(timeout=kill_timeout)
            except (OSError, subprocess.TimeoutExpired):
                pass
        return

    for sig, wait_time in (
        (signal.SIGTERM, term_timeout),
        (signal.SIGKILL, kill_timeout),
    ):
        if process.poll() is not None:
            return
        started = time.monotonic()
        log_event(
            process_logger,
            "process_signal_sent",
            level=logging.DEBUG,
            name=name,
            pid=process.pid,
            pgid=pgid,
            signal=sig.name,
        )
        try:
            os.killpg(pgid, sig)
        except ProcessLookupError:
            return
        try:
            process.wait(timeout=wait_time)
            log_duration(
                process_logger,
                "process_signal_wait",
                time.monotonic() - started,
                name=name,
                pid=process.pid,
                signal=sig.name,
            )
            return
        except subprocess.TimeoutExpired:
            log_duration(
                process_logger,
                "process_signal_wait",
                time.monotonic() - started,
                status="timeout",
                level=logging.WARNING,
                name=name,
                pid=process.pid,
                signal=sig.name,
            )
            continue

    # SIGKILL timed out — the process descriptor must still be
    # reaped to prevent a zombie entry accumulating in the OS process table.
    try:
        process.wait(timeout=0)
    except subprocess.TimeoutExpired:
        log_event(
            process_logger,
            "process_kill_unresponsive",
            level=logging.ERROR,
            name=name,
            pid=process.pid,
            pgid=pgid,
            message="Process did not exit after SIGKILL; descriptor not reaped — possible kernel-level stuck process",
        )