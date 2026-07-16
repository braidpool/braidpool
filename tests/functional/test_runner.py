#!/usr/bin/env python3
"""Run Braidpool functional test scripts."""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import logging
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from test_framework.cleanup_manager import terminate_process_group
from test_framework.constants import STDERR_LOG_NAME, STDOUT_LOG_NAME, TEST_EXIT_PASSED, TEST_EXIT_SKIPPED
from test_framework.logging_utils import configure_stream_logger, log_duration, log_event, log_exception


logger = logging.getLogger(__name__)

# Set of test scripts to run, in order. Extended tests are optional.
BASE_SCRIPTS = [
    "feature_framework_unit_tests.py",
    # TODO: "feature_node_startup.py", (Phase 3 deliverable)
]

EXTENDED_SCRIPTS: list[str] = []


@dataclass(slots=True)
class ScheduledTest:
    """A test command with a stable port seed assigned before scheduling."""

    command: str
    port_seed: int

    @property
    def argv(self) -> list[str]:
        return shlex.split(self.command)

    @property
    def script_name(self) -> str:
        return self.argv[0]

    @property
    def display_name(self) -> str:
        return self.command


@dataclass(slots=True)
class TestResult:
    name: str
    status: str
    duration: float
    testdir: Path
    stdout_path: Path
    stderr_path: Path

    @property
    def was_successful(self) -> bool:
        return self.status in {"Passed", "Skipped"}

    def sort_key(self):
        order = {"Passed": 0, "Skipped": 1, "Failed": 2}
        return order.get(self.status, 3), self.name.lower()

# Class representing one active test subprocess, with methods to check status, detect timeouts, and terminate the process group if needed.
@dataclass(slots=True)
class RunningJob:
    """State for one active test subprocess."""

    scheduled: ScheduledTest
    start_time: float
    process: subprocess.Popen
    testdir: Path
    stdout_path: Path
    stderr_path: Path
    timed_out: bool = False

    @property
    def name(self) -> str:
        return self.scheduled.display_name

    def has_finished(self) -> bool:
        return self.process.poll() is not None

    def has_timed_out(self, now: float, timeout: float | None) -> bool:
        return timeout is not None and now - self.start_time > timeout

    def terminate(self) -> None:
        terminate_process_group(
            self.process,
            name=self.scheduled.script_name,
            term_timeout=2.0,
            kill_timeout=1.0,
            logger=logger,
        )

    def to_result(self) -> TestResult:
        if self.timed_out:
            status = "Failed"
        elif self.process.returncode == TEST_EXIT_PASSED:
            status = "Passed"
        elif self.process.returncode == TEST_EXIT_SKIPPED:
            status = "Skipped"
        else:
            status = "Failed"
        return TestResult(
            name=self.name,
            status=status,
            duration=time.monotonic() - self.start_time,
            testdir=self.testdir,
            stdout_path=self.stdout_path,
            stderr_path=self.stderr_path,
        )


class TestHandler:
    """Launch and monitor functional test script subprocesses."""

    def __init__(
        self,
        *,
        tests_dir: Path,
        tmpdir: Path,
        scheduled_tests: list[ScheduledTest],
        passon_args: list[str],
        jobs: int,
        timeout: float | None,
    ) -> None:
        if jobs < 1:
            raise ValueError("jobs must be >= 1")
        self.tests_dir = tests_dir
        self.tmpdir = tmpdir
        self.test_queue = list(scheduled_tests)
        self.passon_args = passon_args
        self.jobs = jobs
        self.timeout = timeout
        self.running: list[RunningJob] = []

    def done(self) -> bool:
        return not self.test_queue and not self.running

    # Function to check running jobs for completion or timeout, and return finished results. 
    # This is called in a loop until all tests are done, with an optional failfast break. 
    # Also adds newly started jobs to fill available slots up to the configured concurrency level.
    def get_next(self) -> list[TestResult]:
        self._fill_available_slots()

        while True:
            finished: list[TestResult] = []
            now = time.monotonic()
            for job in list(self.running):
                if job.has_finished():
                    self.running.remove(job)
                    finished.append(job.to_result())
                    continue
                if job.has_timed_out(now, self.timeout):
                    job.timed_out = True
                    log_event(logger, "runner_test_timeout", level=logging.ERROR, test=job.name, timeout_seconds=self.timeout)
                    with job.stderr_path.open("ab", buffering=0) as stderr:
                        stderr.write(
                            f"\nTest runner timeout after {self.timeout:.1f}s\n".encode("utf8")
                        )
                    job.terminate()
                    self.running.remove(job)
                    finished.append(job.to_result())

            self._fill_available_slots()

            if finished:
                return finished
            if self.done():
                return []
            time.sleep(0.1)

    def cleanup_running(self) -> None:
        log_event(logger, "runner_cleanup_started", running_jobs=len(self.running))
        for job in list(self.running):
            job.terminate()
        self.running.clear()
        log_event(logger, "runner_cleanup_finished")

    def _fill_available_slots(self) -> None:
        while len(self.running) < self.jobs and self.test_queue:
            self._start(self.test_queue.pop(0))

    # Function to start a test subprocess for a scheduled test, with logs directed to the appropriate files in a test-specific subdirectory. 
    # The process is launched in a new session for easier cleanup, and the RunningJob state is recorded for monitoring.
    
    def _start(self, scheduled: ScheduledTest) -> None:
        test_argv = scheduled.argv
        script_name = test_argv[0]
        test_base = re.sub(r"\.py$", "", script_name)
        testdir = self.tmpdir / f"{test_base}_{scheduled.port_seed}"
        testdir.mkdir(parents=True, exist_ok=True)
        stdout_path = testdir / STDOUT_LOG_NAME
        stderr_path = testdir / STDERR_LOG_NAME
        args = [
            sys.executable,
            str(self.tests_dir / script_name),
            *test_argv[1:],
            *self.passon_args,
            f"--tmpdir={testdir}",
            f"--portseed={scheduled.port_seed}",
        ]
        log_event(
            logger,
            "runner_test_starting",
            test=scheduled.display_name,
            port_seed=scheduled.port_seed,
            stdout_path=stdout_path,
            stderr_path=stderr_path,
        )
        
        stdout_file = None
        stderr_file = None
        try:
            stdout_file = open(stdout_path, "ab", buffering=0)
            stderr_file = open(stderr_path, "ab", buffering=0)
            try:
                proc = subprocess.Popen(
                    args,
                    stdout=stdout_file,
                    stderr=stderr_file,
                    cwd=self.tests_dir,
                    start_new_session=True,
                )
            except Exception as exc:
                log_exception(logger, "runner_test_start_failed", exc, test=scheduled.display_name)
                raise
        finally:
            if stdout_file:
                stdout_file.close()
            if stderr_file:
                stderr_file.close()
        self.running.append(
            RunningJob(
                scheduled=scheduled,
                start_time=time.monotonic(),
                process=proc,
                testdir=testdir,
                stdout_path=stdout_path,
                stderr_path=stderr_path,
            )
        )
        log_event(logger, "runner_test_started", test=scheduled.display_name, pid=proc.pid, port_seed=scheduled.port_seed)


def build_test_list(tests: list[str], *, extended: bool, exclude: str | None, pattern: str | None) -> list[str]:
    available = EXTENDED_SCRIPTS + BASE_SCRIPTS if extended else list(BASE_SCRIPTS)
    if tests:
        selected: list[str] = []
        for test in tests:
            script = Path(test).name
            if not script.endswith(".py"):
                script += ".py"
            matches = [candidate for candidate in available if candidate.split()[0] == script]
            if matches:
                selected.extend(matches)
            elif (Path(__file__).parent / script).exists():
                selected.append(script)
            else:
                raise SystemExit(f"Test {test!r} not found")
    else:
        selected = available

    if exclude:
        excluded = {item if item.endswith(".py") else f"{item}.py" for item in exclude.split(",")}
        selected = [test for test in selected if test.split()[0] not in excluded]

    if pattern:
        regex = re.compile(pattern)
        selected = [test for test in selected if regex.search(test)]

    if not selected:
        raise SystemExit("No valid test scripts selected")
    return selected


def schedule_tests(test_list: list[str]) -> list[ScheduledTest]:
    """Assign stable port seeds before any tests are started."""
    scheduled = [ScheduledTest(command=test, port_seed=index) for index, test in enumerate(test_list)]
    log_event(logger, "runner_tests_scheduled", test_count=len(scheduled), tests=[item.command for item in scheduled])
    return scheduled




# Read last N lines of a file efficiently without loading the whole file, used for printing combined logs on failure with a specified line limit.
def tail_file(path: Path, lines: int) -> str:
    """Return the last *lines* lines without loading the whole file."""
    if lines <= 0 or not path.exists():
        return ""

    chunk_size = 8192
    chunks: list[bytes] = []
    newline_count = 0
    with path.open("rb") as file:
        file.seek(0, os.SEEK_END)
        position = file.tell()
        while position > 0 and newline_count <= lines:
            read_size = min(chunk_size, position)
            position -= read_size
            file.seek(position)
            chunk = file.read(read_size)
            chunks.append(chunk)
            newline_count += chunk.count(b"\n")

    data = b"".join(reversed(chunks))
    return "\n".join(data.decode("utf8", errors="replace").splitlines()[-lines:])


def print_results(results: list[TestResult], runtime: float) -> None:
    max_name = max(len(result.name) for result in results) if results else 4
    print("\n{} | STATUS  | DURATION".format("TEST".ljust(max_name)))
    print("-" * (max_name + 23))
    for result in sorted(results, key=TestResult.sort_key):
        print(f"{result.name.ljust(max_name)} | {result.status.ljust(7)} | {result.duration:.3f}s")
    all_passed = all(result.was_successful for result in results)
    status = "Passed" if all_passed else "Failed"
    print("-" * (max_name + 23))
    print(f"{'ALL'.ljust(max_name)} | {status.ljust(7)} | {runtime:.3f}s")


def write_results(results: list[TestResult], filepath: Path, runtime: float) -> None:
    with filepath.open("w", newline="", encoding="utf8") as output:
        writer = csv.writer(output)
        writer.writerow(["test", "status", "duration_seconds"])
        all_passed = True
        for result in results:
            all_passed = all_passed and result.was_successful
            writer.writerow([result.name, result.status, result.duration])
        writer.writerow(["ALL", "Passed" if all_passed else "Failed", runtime])


def parse_args(argv: Sequence[str]) -> tuple[argparse.Namespace, list[str]]:
    parser = argparse.ArgumentParser(
        usage="%(prog)s [test_runner.py options] [scripts] [-- script options]",
        description=__doc__,
    )
    parser.add_argument("--combinedlogslen", "-c", type=int, default=0)
    parser.add_argument("--exclude", "-x")
    parser.add_argument("--extended", action="store_true")
    parser.add_argument("--failfast", "-F", action="store_true")
    parser.add_argument("--filter")
    parser.add_argument("--jobs", "-j", type=int, default=1)
    parser.add_argument("--nocleanup", action="store_true")
    parser.add_argument("--resultsfile", "-r", type=Path)
    parser.add_argument("--timeout", type=float, default=600.0, help="runner timeout per test script in seconds")
    parser.add_argument("--tmpdirprefix", "-t", default=tempfile.gettempdir())
    parser.add_argument("tests", nargs="*")

    return parser.parse_known_args(argv)

# Main function to parse arguments, build the test list, schedule tests with port seeds, 
# and use TestHandler to run and monitor the tests while collecting results.
# It assigns the port seeds before starting any tests using helper functions, 
# and handles printing results and cleanup based on success or failure.
def main() -> int:
    configure_stream_logger(__name__)
    args, passon_args = parse_args(sys.argv[1:])
    if args.nocleanup:
        passon_args.append("--nocleanup")

    test_list = build_test_list(args.tests, extended=args.extended, exclude=args.exclude, pattern=args.filter)
    scheduled_tests = schedule_tests(test_list)
    timestamp = dt.datetime.now(tz=dt.timezone.utc).strftime("%Y%m%d_%H%M%S")
    prefix = f"bp_func_test_runner_{timestamp}_"
    tmpdir_str = tempfile.mkdtemp(prefix=prefix, dir=args.tmpdirprefix)
    tmpdir = Path(tmpdir_str)
    log_event(logger, "runner_started", tmpdir=tmpdir, jobs=args.jobs, timeout_seconds=args.timeout)

    tests_dir = Path(__file__).resolve().parent
    handler = TestHandler(
        tests_dir=tests_dir,
        tmpdir=tmpdir,
        scheduled_tests=scheduled_tests,
        passon_args=passon_args,
        jobs=args.jobs,
        timeout=args.timeout if args.timeout > 0 else None,
    )
    start_time = time.monotonic()
    results: list[TestResult] = []
    all_passed = True

    try:
        while not handler.done():
            if args.failfast and not all_passed:
                break
            for result in handler.get_next():
                results.append(result)
                log_duration(
                    logger,
                    "runner_test_finished",
                    result.duration,
                    status=result.status.lower(),
                    test=result.name,
                )
                if result.status == "Failed":
                    all_passed = False
                    print(f"\n{result.name} failed after {result.duration:.3f}s")
                    if args.combinedlogslen:
                        stdout_tail = tail_file(result.stdout_path, args.combinedlogslen)
                        stderr_tail = tail_file(result.stderr_path, args.combinedlogslen)
                        if stdout_tail:
                            print("\nstdout tail:\n" + stdout_tail)
                        if stderr_tail:
                            print("\nstderr tail:\n" + stderr_tail)
    except KeyboardInterrupt:
        all_passed = False
        log_event(logger, "runner_interrupted", level=logging.WARNING)
    finally:
        handler.cleanup_running()

    runtime = time.monotonic() - start_time
    print_results(results, runtime)
    if args.resultsfile:
        write_results(results, args.resultsfile, runtime)

    if all_passed and not args.nocleanup:
        shutil.rmtree(tmpdir, ignore_errors=True)
    else:
        print(f"Test data left in {tmpdir}")

    log_duration(logger, "runner_finished", time.monotonic() - start_time, status="passed" if all_passed else "failed")
    return 0 if all_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
