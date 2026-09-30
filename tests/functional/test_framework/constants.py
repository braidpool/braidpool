"""Shared constants for Braidpool functional tests."""

from __future__ import annotations

TEST_EXIT_PASSED = 0
TEST_EXIT_FAILED = 1
TEST_EXIT_SKIPPED = 77

FRAMEWORK_LOG_NAME = "test_framework.log"
STDOUT_LOG_NAME = "stdout.log"
STDERR_LOG_NAME = "stderr.log"
LOG_NAMES = (FRAMEWORK_LOG_NAME, STDOUT_LOG_NAME, STDERR_LOG_NAME)
