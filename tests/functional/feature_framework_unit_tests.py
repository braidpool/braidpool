#!/usr/bin/env python3
"""Self-tests for the Braidpool functional test framework (Phases 1–3)."""

from __future__ import annotations

import argparse
import json
import logging
import os
import subprocess
import stat
import sys
import tempfile
import time
from collections.abc import Callable
from pathlib import Path
from unittest.mock import ANY, Mock, call, patch

from test_runner import (
    RunningJob,
    ScheduledTest,
    build_test_list,
    parse_args,
    schedule_tests,
    tail_file,
)
from test_framework.cleanup_manager import CleanupManager
from test_framework.constants import (
    STDERR_LOG_NAME,
    STDOUT_LOG_NAME,
    TEST_EXIT_PASSED,
    TEST_EXIT_SKIPPED,
)
from test_framework.log_manager import LogManager
from test_framework.logging_utils import (
    configure_file_logger,
    configure_stream_logger,
    log_duration,
    log_event,
    log_exception,
    log_rpc_call,
)
from test_framework.network_config import NetworkConfig
from test_framework.port_pool import PortAllocationError, PortPool, PortSeed
from test_framework.rpc_client import (
    RpcClient,
    RpcError,
    RpcInvalidResponseError,
    RpcTimeoutError,
    RpcTransportError,
)
from test_framework.util import SkipTest, assert_equal, find_binary, wait_until


def test_network_config_defaults() -> None:
    cfg = NetworkConfig()
    assert_equal(cfg.num_braidpool_nodes, 1)
    assert_equal(cfg.network, "regtest")
    assert_equal(cfg.initial_blocks, 101)
    assert cfg.bitcoin_rpc_port is None
    assert cfg.bitcoin_p2p_port is None
    assert cfg.bitcoin_ipc_socket is None
    assert cfg.bitcoin_bin_path is None
    assert cfg.braidpool_bin_path is None
    assert_equal(cfg.startup_timeout_braidpool, 30.0)
    assert_equal(cfg.startup_timeout_btc, 90.0)
    assert_equal(cfg.rpc_timeout, 10.0)
    assert_equal(cfg.peer_connection_timeout, 15.0)
    assert_equal(cfg.bead_propagation_timeout, 60.0)
    assert_equal(cfg.log_level, "INFO")
    assert_equal(cfg.random_seed, 42)


def test_port_pool_deterministic_band() -> None:
    pool = PortPool(port_seed=3, validate_ports=False)
    assert_equal(pool.band, (16300, 16399))
    assert_equal(pool.allocate("bitcoin_rpc"), 16300)
    assert_equal(pool.allocate("braidpool_p2p", node_id=2), 16312)
    assert_equal(pool.allocate("braidpool_rpc", node_id=2), 16342)
    assert_equal(pool.allocate("braidpool_stratum", node_id=2), 16372)


def test_port_seed_global_default() -> None:
    old_seed = PortSeed.n
    try:
        PortSeed.n = 4
        pool = PortPool(validate_ports=False)
        assert_equal(pool.band, (16400, 16499))
    finally:
        PortSeed.n = old_seed


def test_port_pool_auto_select_skips_ephemeral_range() -> None:
    original_probe = PortPool._bind_probe
    original_udp_probe = PortPool._udp_bind_probe
    original_ephemeral_range = PortPool._linux_ephemeral_range

    def no_op_probe(port: int) -> None:
        assert 1 <= port <= PortPool.MAX_PORT

    try:
        PortPool._bind_probe = staticmethod(no_op_probe)
        PortPool._udp_bind_probe = staticmethod(no_op_probe)
        PortPool._linux_ephemeral_range = staticmethod(lambda: (32800, 60999))
        pool = PortPool(port_seed=168, auto_select_port_seed=True)
        assert_equal(pool.port_seed, 450)
        assert_equal(pool.band, (61000, 61099))
    finally:
        PortPool._bind_probe = staticmethod(original_probe)
        PortPool._udp_bind_probe = staticmethod(original_udp_probe)
        PortPool._linux_ephemeral_range = staticmethod(original_ephemeral_range)


def test_port_pool_auto_select_skips_udp_occupied_p2p_port() -> None:
    original_probe = PortPool._bind_probe
    original_udp_probe = PortPool._udp_bind_probe
    original_ephemeral_range = PortPool._linux_ephemeral_range
    occupied_port = PortPool.BASE_PORT + PortPool._COMPONENT_RANGES["braidpool_p2p"].start

    def no_op_probe(port: int) -> None:
        assert 1 <= port <= PortPool.MAX_PORT

    def udp_probe_with_collision(port: int) -> None:
        if port == occupied_port:
            raise OSError("simulated occupied UDP port")

    try:
        PortPool._bind_probe = staticmethod(no_op_probe)
        PortPool._udp_bind_probe = staticmethod(udp_probe_with_collision)
        PortPool._linux_ephemeral_range = staticmethod(lambda: None)
        pool = PortPool(port_seed=0, auto_select_port_seed=True)
        assert_equal(pool.port_seed, 1)
    finally:
        PortPool._bind_probe = staticmethod(original_probe)
        PortPool._udp_bind_probe = staticmethod(original_udp_probe)
        PortPool._linux_ephemeral_range = staticmethod(original_ephemeral_range)


def test_port_pool_auto_select_stays_within_tcp_port_range() -> None:
    original_probe = PortPool._bind_probe
    original_ephemeral_range = PortPool._linux_ephemeral_range
    probed_ports: list[int] = []

    def fake_probe(port: int) -> None:
        probed_ports.append(port)
        raise OSError("simulated occupied port")

    try:
        PortPool._bind_probe = staticmethod(fake_probe)
        PortPool._linux_ephemeral_range = staticmethod(lambda: None)
        try:
            PortPool(port_seed=494, auto_select_port_seed=True)
        except PortAllocationError:
            assert probed_ports
            assert max(probed_ports) <= PortPool.MAX_PORT
            return
    finally:
        PortPool._bind_probe = staticmethod(original_probe)
        PortPool._linux_ephemeral_range = staticmethod(original_ephemeral_range)
    raise AssertionError("auto-selection did not report exhausted valid port bands")


def test_port_pool_manual_collision() -> None:
    pool = PortPool(port_seed=5, validate_ports=False)
    port = pool.allocate("bitcoin_rpc")
    try:
        pool.reserve_manual("manual", [port])
    except PortAllocationError:
        return
    raise AssertionError("manual port collision was not detected")


def test_port_pool_bind_failure_is_reported() -> None:
    pool = PortPool(port_seed=6)
    failing_port = 16691
    original_probe = PortPool._bind_probe

    def fake_probe(port: int) -> None:
        if port == failing_port:
            raise OSError("simulated occupied port")

    try:
        PortPool._bind_probe = staticmethod(fake_probe)
        assert_equal(pool.allocate("helper"), 16690)
        try:
            pool.allocate("helper")
        except PortAllocationError:
            return
    finally:
        PortPool._bind_probe = staticmethod(original_probe)
    raise AssertionError("occupied deterministic port was not reported")


def test_port_pool_udp_bind_failure_is_reported() -> None:
    original_probe = PortPool._bind_probe
    original_udp_probe = PortPool._udp_bind_probe
    failing_port = 16610

    def no_op_probe(port: int) -> None:
        assert 1 <= port <= PortPool.MAX_PORT

    def failing_udp_probe(port: int) -> None:
        if port == failing_port:
            raise OSError("simulated occupied UDP port")

    try:
        PortPool._bind_probe = staticmethod(no_op_probe)
        PortPool._udp_bind_probe = staticmethod(failing_udp_probe)
        pool = PortPool(port_seed=6)
        try:
            pool.allocate("braidpool_p2p", node_id=0)
        except PortAllocationError:
            return
    finally:
        PortPool._bind_probe = staticmethod(original_probe)
        PortPool._udp_bind_probe = staticmethod(original_udp_probe)
    raise AssertionError("occupied UDP port was not reported")


def test_log_manager_paths_and_cleanup() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp) / "case"
        logs = LogManager(tmpdir, "phase1")
        stdout, stderr = logs.get_process_log_files("node0")
        assert_equal(stdout, tmpdir / "node0" / STDOUT_LOG_NAME)
        assert_equal(stderr, tmpdir / "node0" / STDERR_LOG_NAME)
        assert logs.framework_log.exists()
        assert logs.reports_dir().exists()
        logs.cleanup(passed=False)
        assert tmpdir.exists()
        logs.cleanup(passed=True)
        assert not tmpdir.exists()


def test_log_manager_nocleanup() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp) / "case"
        logs = LogManager(tmpdir, "phase1")
        logs.cleanup(passed=True, nocleanup=True)
        assert tmpdir.exists()


def test_wait_until() -> None:
    state = {"count": 0}

    def predicate() -> bool:
        state["count"] += 1
        return state["count"] >= 2

    wait_until(predicate, timeout=1.0, interval=0.01)


def test_runner_args_parsing() -> None:
    runner_args, script_args = parse_args(
        ["--jobs=2", "feature_framework_unit_tests.py", "--custom-flag", "value"]
    )
    assert_equal(runner_args.jobs, 2)
    assert_equal(runner_args.tests, ["feature_framework_unit_tests.py"])
    assert_equal(script_args, ["--custom-flag", "value"])


def test_runner_args_unknown_passthrough() -> None:
    runner_args, script_args = parse_args(
        ["feature_framework_unit_tests.py", "--unknown-runner-flag"]
    )
    assert_equal(runner_args.tests, ["feature_framework_unit_tests.py"])
    assert_equal(script_args, ["--unknown-runner-flag"])


def test_runner_stable_port_seeds() -> None:
    original_probe = PortPool._bind_probe
    original_ephemeral_range = PortPool._linux_ephemeral_range

    def no_op_probe(port: int) -> None:
        assert 1 <= port <= PortPool.MAX_PORT

    try:
        PortPool._bind_probe = staticmethod(no_op_probe)
        PortPool._linux_ephemeral_range = staticmethod(lambda: None)
        scheduled = schedule_tests(["a.py", "b.py --arg", "c.py"])
    finally:
        PortPool._bind_probe = staticmethod(original_probe)
        PortPool._linux_ephemeral_range = staticmethod(original_ephemeral_range)

    assert_equal([item.port_seed for item in scheduled], [0, 1, 2])
    assert_equal([item.command for item in scheduled], ["a.py", "b.py --arg", "c.py"])


def test_runner_default_selection_and_filters() -> None:
    expected = [
        "feature_framework_lifecycle.py",
        "feature_framework_skip.py",
        "feature_framework_unit_tests.py",
        "feature_node_startup.py",
        "feature_mining_block_acceptance.py",
    ]
    assert_equal(build_test_list([], extended=False, exclude=None, pattern=None), expected)
    assert_equal(
        build_test_list([], extended=False, exclude="feature_node_startup", pattern=None),
        [
            "feature_framework_lifecycle.py",
            "feature_framework_skip.py",
            "feature_framework_unit_tests.py",
            "feature_mining_block_acceptance.py",
        ],
    )
    assert_equal(
        build_test_list([], extended=False, exclude=None, pattern="node_startup"),
        ["feature_node_startup.py"],
    )


def test_runner_result_status_mapping() -> None:
    class FakeProcess:
        def __init__(self, returncode: int) -> None:
            self.returncode = returncode

    def make_result(returncode: int, *, timed_out: bool = False):
        job = RunningJob(
            scheduled=ScheduledTest("dummy.py", 0),
            start_time=0.0,
            process=FakeProcess(returncode),  # type: ignore[arg-type]
            testdir=Path("/tmp/dummy"),
            stdout_path=Path("/tmp/dummy/stdout.log"),
            stderr_path=Path("/tmp/dummy/stderr.log"),
            timed_out=timed_out,
        )
        return job.to_result()

    passed = make_result(TEST_EXIT_PASSED)
    skipped = make_result(TEST_EXIT_SKIPPED)
    failed = make_result(1)
    timed_out = make_result(TEST_EXIT_PASSED, timed_out=True)

    assert_equal(passed.status, "Passed")
    assert passed.was_successful
    assert_equal(skipped.status, "Skipped")
    assert skipped.was_successful
    assert_equal(failed.status, "Failed")
    assert not failed.was_successful
    assert_equal(timed_out.status, "Failed")


def test_tail_file_reads_suffix() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "log.txt"
        path.write_text("".join(f"line-{i}\n" for i in range(100)), encoding="utf8")
        assert_equal(tail_file(path, 3), "line-97\nline-98\nline-99")


def test_structured_logging_utils() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "framework.log"
        logger = configure_file_logger("braidpool.functional.selftest", path, level="DEBUG")
        log_event(logger, "plain_event", password="hidden", visible="value")
        log_duration(logger, "duration_event", 0.125, component="selftest")
        log_rpc_call(
            logger,
            "bitcoinproxy",
            0.25,
            status="ok",
            request_id=7,
            params={"rpcpass": "hidden", "method": "getblockchaininfo"},
        )
        try:
            raise ValueError("expected failure")
        except ValueError as exc:
            log_exception(logger, "exception_event", exc, token="hidden")
        for handler in logger.handlers:
            handler.flush()

        raw = path.read_text(encoding="utf8")
        assert "hidden" not in raw
        assert "<redacted>" in raw
        records = [json.loads(line) for line in raw.splitlines()]
        events = [record["event"] for record in records]
        assert "plain_event" in events
        assert "duration_event" in events
        assert "rpc_call" in events
        assert "exception_event" in events
        assert "exception_event_traceback" in events


def test_rpc_client_success_and_wrapper_mapping() -> None:
    calls: list[dict] = []

    def transport(_url: str, payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        request = json.loads(payload.decode("utf8"))
        calls.append(request)
        return json.dumps({"jsonrpc": "2.0", "id": request["id"], "result": {"ok": True}}).encode("utf8")

    client = RpcClient("127.0.0.1", 1234, transport=transport)
    assert_equal(client.get_bead("abc"), {"ok": True})
    assert_equal(calls[0]["method"], "getbead")
    assert_equal(calls[0]["params"], ["abc"])


def test_rpc_client_error_preserves_code_and_message() -> None:
    def transport(_url: str, payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        request = json.loads(payload.decode("utf8"))
        return json.dumps(
            {
                "jsonrpc": "2.0",
                "id": request["id"],
                "error": {"code": -8, "message": "bad bead"},
            }
        ).encode("utf8")

    client = RpcClient("127.0.0.1", 1234, transport=transport)
    try:
        client.get_bead("abc")
    except RpcError as exc:
        assert_equal(exc.code, -8)
        assert_equal(exc.message, "bad bead")
        return
    raise AssertionError("JSON-RPC error was not raised")


def test_rpc_client_retries_connection_refused() -> None:
    attempts = {"count": 0}

    def transport(_url: str, payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        attempts["count"] += 1
        if attempts["count"] < 3:
            raise ConnectionRefusedError("not ready")
        request = json.loads(payload.decode("utf8"))
        return json.dumps({"jsonrpc": "2.0", "id": request["id"], "result": 7}).encode("utf8")

    client = RpcClient("127.0.0.1", 1234, max_retries=3, retry_delay=0, transport=transport)
    assert_equal(client.get_bead_count(), 7)
    assert_equal(attempts["count"], 3)


def test_rpc_client_transport_failure_after_retries() -> None:
    def transport(_url: str, _payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        raise ConnectionRefusedError("not ready")

    client = RpcClient("127.0.0.1", 1234, max_retries=1, retry_delay=0, transport=transport)
    try:
        client.get_bead_count()
    except RpcTransportError:
        return
    raise AssertionError("transport failure was not raised")


def test_rpc_client_timeout() -> None:
    def transport(_url: str, _payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        raise TimeoutError("slow")

    client = RpcClient("127.0.0.1", 1234, retry_delay=0, transport=transport)
    try:
        client.get_bead_count()
    except RpcTimeoutError:
        return
    raise AssertionError("timeout was not raised")


def test_rpc_client_invalid_response() -> None:
    def transport(_url: str, _payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        return b"not-json"

    client = RpcClient("127.0.0.1", 1234, retry_delay=0, transport=transport)
    try:
        client.get_bead_count()
    except RpcInvalidResponseError:
        return
    raise AssertionError("invalid response was not raised")


def test_mock_miner_retries_early_eof() -> None:
    from test_framework.mock_miner import MockStratumMiner

    logger = Mock()
    miner = MockStratumMiner(12345, logger=logger)
    closed_connection = Mock()
    closed_connection.recv.return_value = b""
    subscribed_connection = Mock()
    subscribed_connection.recv.return_value = (
        b'{"id":1,"result":[[], "abcd", 4],"error":null}\n'
    )
    connections = [closed_connection, subscribed_connection]
    original_request = miner._request

    def request(method: str, params: list[object]) -> object:
        if method == "mining.subscribe":
            return original_request(method, params)
        if method in ("mining.authorize", "mining.submit"):
            return True
        raise AssertionError(f"Unexpected Stratum request: {method}")

    def select_readable(readers, *_args):
        readable = [
            reader
            for reader in readers
            if (
                reader is closed_connection
                and closed_connection.recv.call_count == 0
            )
            or (
                reader is subscribed_connection
                and subscribed_connection.recv.call_count == 0
            )
        ]
        return readable, [], []

    with (
        patch(
            "test_framework.mock_miner.socket.create_connection",
            side_effect=connections,
        ) as create_connection,
        patch(
            "test_framework.mock_miner.select.select",
            side_effect=select_readable,
        ),
        patch.object(miner, "_request", side_effect=request),
        patch.object(
            miner,
            "_wait_for_job",
            return_value=(0.01, {"job_id": "job", "ntime": "00000000"}),
        ),
        patch.object(miner, "_find_nonce", return_value="00000000"),
    ):
        result = miner.mine_one_block(timeout=1.0)

    assert_equal(result.job_id, "job")
    assert_equal(create_connection.call_count, 2)
    closed_connection.recv.assert_called_once_with(4096)
    subscribed_connection.recv.assert_called_once_with(4096)
    closed_connection.close.assert_called()
    events = [
        log_call.kwargs["extra"]["bp_event"]
        for log_call in logger.log.call_args_list
    ]
    assert_equal(events.count("miner_session_closed"), 1)


def test_mock_miner_header_hash_fixture() -> None:
    from test_framework.mock_miner import MockStratumMiner

    miner = MockStratumMiner(12345)
    miner._deadline = time.monotonic() + 10.0
    job = {
        "coinbase1": "010203",
        "coinbase2": "aabb",
        "prevhash": bytes(range(32)).hex(),
        "merkle_branches": [bytes(range(32, 64)).hex()],
        "version": "20000000",
        "bits": "1f400000",
        "ntime": "00000001",
    }
    expected_header_prefix = bytes.fromhex(
        "00000020"
        "03020100070605040b0a09080f0e0d0c"
        "13121110171615141b1a19181f1e1d1c"
        "ac9d09a0279ed605e6fa134c3caecac1"
        "b35afbd90bd2f6c7243e325631ed5660"
        "01000000"
        "0000401f"
    )
    expected_block_hash = (
        "87657fb9c83cb4f833d72f919e9b99b1219d6efd24a4151a717e47cb43802b00"
    )
    hashed_headers: list[tuple[bytes, bytes]] = []
    original_double_sha256 = miner._double_sha256

    def record_double_sha256(data: bytes) -> bytes:
        digest = original_double_sha256(data)
        if len(data) == 80:
            hashed_headers.append((data, digest))
        return digest

    with patch.object(miner, "_double_sha256", side_effect=record_double_sha256):
        nonce = miner._find_nonce(job, "a1b2", 2)

    assert_equal(nonce, "000000b4")
    assert hashed_headers, "Mock miner did not hash a block header"
    header, block_hash = hashed_headers[-1]
    assert_equal(header[:76], expected_header_prefix)
    assert_equal(header[76:], bytes.fromhex("b4000000"))
    assert_equal(block_hash.hex(), expected_block_hash)
    target = 0x400000 << 224
    assert int.from_bytes(block_hash, "little") <= target


def test_mock_miner_returns_on_nbits() -> None:
    from test_framework.mock_miner import MockStratumMiner

    miner = MockStratumMiner(12345)
    miner._difficulty = 0.01
    miner._deadline = time.monotonic() + 10.0
    job = {
        "coinbase1": "010203",
        "coinbase2": "aabb",
        "prevhash": "00" * 32,
        "merkle_branches": [],
        "version": "20000000",
        "bits": "207fffff",
        "ntime": "00000001",
    }
    block_target = miner._target_from_compact(0x207FFFFF)
    share_target = miner._target_from_difficulty(miner._difficulty)
    block_only_hash = ((block_target + share_target) // 2).to_bytes(32, "little")
    with patch.object(
        miner,
        "_double_sha256",
        side_effect=[bytes(32), block_only_hash],
    ):
        nonce = miner._find_nonce(job, "abcd", 2, extranonce2=bytes(2))

    assert share_target < block_target
    assert int.from_bytes(block_only_hash, "little") <= block_target
    assert int.from_bytes(block_only_hash, "little") > share_target
    assert_equal(nonce, "00000000")


def test_mock_miner_continues_after_share() -> None:
    from test_framework.mock_miner import MockStratumMiner

    logger = Mock()
    miner = MockStratumMiner(12345, logger=logger)
    miner._socket = Mock()
    miner._difficulty = 0.5
    miner._deadline = time.monotonic() + 10.0
    miner._current_job = {
        "job_id": "job",
        "coinbase1": "010203",
        "coinbase2": "aabb",
        "prevhash": "00" * 32,
        "merkle_branches": [],
        "version": "20000000",
        "bits": "1d00ffff",
        "ntime": "00000001",
    }
    miner._extranonce1 = "abcd"
    miner._extranonce2_size = 2
    block_target = miner._target_from_compact(0x1D00FFFF)
    share_target = miner._target_from_difficulty(miner._difficulty)
    share_only_hash = ((block_target + share_target) // 2).to_bytes(32, "little")

    with (
        patch.object(
            miner,
            "_double_sha256",
            side_effect=[bytes(32), share_only_hash, bytes(32)],
        ),
        patch.object(miner, "_request", return_value=True) as request,
        patch.object(miner, "_process_available_notifications"),
    ):
        result = miner._mine_current_job()

    assert share_target > block_target
    assert int.from_bytes(share_only_hash, "little") <= share_target
    assert int.from_bytes(share_only_hash, "little") > block_target
    assert_equal(result.nonce, "00000001")
    assert_equal(request.call_count, 2)
    request.assert_has_calls(
        [
            call(
                "mining.submit",
                ["mock-miner", "job", "0000", "00000001", "00000000"],
            ),
            call(
                "mining.submit",
                ["mock-miner", "job", "0000", "00000001", "00000001"],
            ),
        ]
    )
    assert_equal(
        [
            log_call.kwargs["extra"]["bp_event"]
            for log_call in logger.log.call_args_list
        ],
        [
            "miner_mining_started",
            "miner_share_submitted",
            "miner_block_submitted",
        ],
    )


def test_mock_miner_rejects_share_submission() -> None:
    from test_framework.mock_miner import MockStratumMiner, SubmissionRejectedError

    logger = Mock()
    miner = MockStratumMiner(12345, logger=logger)
    miner._socket = Mock()
    miner._difficulty = 0.5
    miner._deadline = time.monotonic() + 10.0
    miner._current_job = {
        "job_id": "job",
        "coinbase1": "010203",
        "coinbase2": "aabb",
        "prevhash": "00" * 32,
        "merkle_branches": [],
        "version": "20000000",
        "bits": "1d00ffff",
        "ntime": "00000001",
    }
    miner._extranonce1 = "abcd"
    miner._extranonce2_size = 2
    block_target = miner._target_from_compact(0x1D00FFFF)
    share_target = miner._target_from_difficulty(miner._difficulty)
    share_only_hash = ((block_target + share_target) // 2).to_bytes(32, "little")

    with (
        patch.object(
            miner,
            "_double_sha256",
            side_effect=[bytes(32), share_only_hash],
        ),
        patch.object(miner, "_request", return_value=False) as request,
        patch.object(miner, "_process_available_notifications"),
    ):
        try:
            miner._mine_current_job()
        except SubmissionRejectedError as exc:
            assert_equal(str(exc), "Stratum server rejected share for job job")
        else:
            raise AssertionError("rejected share was accepted")

    request.assert_called_once_with(
        "mining.submit",
        ["mock-miner", "job", "0000", "00000001", "00000000"],
    )
    assert_equal(
        [
            log_call.kwargs["extra"]["bp_event"]
            for log_call in logger.log.call_args_list
        ],
        ["miner_mining_started", "miner_share_rejected"],
    )


def test_mock_miner_rejects_invalid_set_difficulty() -> None:
    from test_framework.mock_miner import MockMinerProtocolError, MockStratumMiner

    invalid_difficulties = (True, 0, -1, float("nan"), float("inf"), 10**400)
    for difficulty in invalid_difficulties:
        miner = MockStratumMiner(12345)
        notification = {
            "id": None,
            "method": "mining.set_difficulty",
            "params": [difficulty],
        }
        with patch.object(miner, "_receive", return_value=notification):
            try:
                miner._wait_for_job()
            except MockMinerProtocolError as exc:
                assert_equal(
                    str(exc), "Invalid mining.set_difficulty notification"
                )
            else:
                raise AssertionError(
                    f"Invalid difficulty {difficulty!r} was accepted"
                )


def test_mock_miner_rejects_authorization() -> None:
    from test_framework.mock_miner import (
        MockMinerAuthorizationError,
        MockStratumMiner,
    )

    miner = MockStratumMiner(12345)
    connection = Mock()
    with (
        patch(
            "test_framework.mock_miner.socket.create_connection",
            return_value=connection,
        ),
        patch.object(miner, "_subscribe", return_value=("abcd", 4)),
        patch.object(miner, "_request", return_value=False) as request,
    ):
        try:
            miner.mine_one_block(timeout=1.0)
        except MockMinerAuthorizationError as exc:
            assert "rejected miner authorization" in str(exc)
        else:
            raise AssertionError("rejected authorization was accepted")

    request.assert_called_once_with("mining.authorize", ["mock-miner", "x"])
    connection.close.assert_called_once()


def test_mock_miner_rejects_unaccepted_submission() -> None:
    from test_framework.mock_miner import (
        SubmissionRejectedError,
        MockStratumMiner,
    )

    miner = MockStratumMiner(12345)
    connection = Mock()
    with (
        patch(
            "test_framework.mock_miner.socket.create_connection",
            return_value=connection,
        ),
        patch.object(miner, "_subscribe", return_value=("abcd", 4)),
        patch.object(miner, "_request", side_effect=[True, False]) as request,
        patch.object(
            miner,
            "_wait_for_job",
            return_value=(0.01, {"job_id": "job", "ntime": "00000000"}),
        ),
        patch(
            "test_framework.mock_miner.select.select",
            return_value=([], [], []),
        ),
        patch.object(miner, "_find_nonce", return_value="00000000"),
    ):
        try:
            miner.mine_one_block(timeout=1.0)
        except SubmissionRejectedError as exc:
            assert_equal(str(exc), "Stratum server rejected mined job job")
        else:
            raise AssertionError("unaccepted mining submission was accepted")

    request.assert_has_calls(
        [
            call("mining.authorize", ["mock-miner", "x"]),
            call(
                "mining.submit",
                ["mock-miner", "job", "00000000", "00000000", "00000000"],
            ),
        ]
    )
    assert_equal(request.call_count, 2)
    connection.close.assert_called_once()


def test_mock_miner_categorizes_stratum_request_errors() -> None:
    from test_framework.mock_miner import (
        MockMinerAuthorizationError,
        MockMinerRequestError,
        SubmissionRejectedError,
        MockStratumMiner,
    )

    error_types = (
        ("mining.authorize", MockMinerAuthorizationError),
        ("mining.submit", SubmissionRejectedError),
        ("mining.subscribe", MockMinerRequestError),
    )
    for method, error_type in error_types:
        miner = MockStratumMiner(12345)
        miner._socket = Mock()
        with (
            patch.object(miner, "_send"),
            patch.object(
                miner,
                "_receive",
                return_value={
                    "id": 1,
                    "error": {"code": -1, "message": "request rejected"},
                },
            ),
        ):
            try:
                miner._request(method, [])
            except error_type as exc:
                assert method in str(exc)
            else:
                raise AssertionError(f"{method} error was not categorized")


def _mock_stratum_message(payload: dict[str, object]) -> bytes:
    return (json.dumps(payload) + "\n").encode("utf8")


def _mock_mining_notify(
    job_id: str, prevhash: str, *, clean_jobs: bool = True
) -> bytes:
    return _mock_stratum_message(
        {
            "id": None,
            "method": "mining.notify",
            "params": [
                job_id,
                prevhash,
                "010203",
                "aabb",
                [],
                "20000000",
                "1f400000",
                "00000001",
                clean_jobs,
            ],
        }
    )


def test_mock_miner_session_reuses_pushed_jobs() -> None:
    from test_framework.mock_miner import MockStratumMiner

    connection = Mock()
    connection.recv.side_effect = [
        _mock_stratum_message({"id": 1, "result": [[], "abcd", 4], "error": None}),
        b"".join(
            [
                _mock_stratum_message({"id": 2, "result": True, "error": None}),
                _mock_stratum_message(
                    {
                        "id": None,
                        "method": "mining.set_difficulty",
                        "params": [0.01],
                    }
                ),
                _mock_mining_notify("job-1", "00" * 32),
            ]
        ),
        _mock_mining_notify("job-2", "11" * 32, clean_jobs=False),
        _mock_stratum_message({"id": 3, "result": True, "error": None}),
        _mock_stratum_message({"id": 4, "result": True, "error": None}),
    ]
    miner = MockStratumMiner(12345)
    searches_with_notifications = {1}
    notified_searches: set[int] = set()

    def select_readable(readers, _writers, _errors, timeout):
        if timeout == 0:
            search_count = find_nonce.call_count
            if (
                search_count in searches_with_notifications
                and search_count not in notified_searches
            ):
                notified_searches.add(search_count)
                return readers, [], []
            return [], [], []
        return readers, [], []

    with (
        patch(
            "test_framework.mock_miner.socket.create_connection",
            return_value=connection,
        ) as create_connection,
        patch(
            "test_framework.mock_miner.select.select",
            side_effect=select_readable,
        ),
        patch.object(
            miner, "_find_nonce", side_effect=["00000000", "00000001"]
        ) as find_nonce,
    ):
        with miner.session(timeout=1.0):
            first_job = miner.current_job
            first_result = miner.mine_current_job(timeout=1.0)
            assert_equal(first_result.job_id, "job-1")
            connection.close.assert_not_called()

            difficulty, next_job = miner.wait_for_next_job(timeout=1.0)
            assert_equal(difficulty, 0.01)
            assert_equal(next_job["job_id"], "job-2")
            second_result = miner.mine_current_job(timeout=1.0)
            assert_equal(second_result.job_id, "job-2")
            connection.close.assert_not_called()

    create_connection.assert_called_once()
    connection.close.assert_called_once()
    submissions = [
        json.loads(sent.args[0].decode("utf8"))
        for sent in connection.sendall.call_args_list
        if json.loads(sent.args[0].decode("utf8"))["method"] == "mining.submit"
    ]
    assert_equal(
        [submission["params"][1] for submission in submissions],
        ["job-1", "job-2"],
    )
    assert_equal(
        [submission["params"][2] for submission in submissions],
        ["00000000", "00000001"],
    )
    find_nonce.assert_has_calls(
        [
            call(
                first_job,
                "abcd",
                4,
                extranonce2=bytes.fromhex("00000000"),
                on_share=ANY,
            ),
            call(
                next_job,
                "abcd",
                4,
                extranonce2=bytes.fromhex("00000001"),
                on_share=ANY,
            ),
        ]
    )


def test_mock_miner_stages_extranonce_until_next_job() -> None:
    from test_framework.mock_miner import MockStratumMiner

    connection = Mock()
    connection.recv.side_effect = [
        _mock_stratum_message({"id": 1, "result": [[], "abcd", 4], "error": None}),
        b"".join(
            [
                _mock_stratum_message({"id": 2, "result": True, "error": None}),
                _mock_stratum_message(
                    {
                        "id": None,
                        "method": "mining.set_difficulty",
                        "params": [0.01],
                    }
                ),
                _mock_mining_notify("job-1", "00" * 32),
            ]
        ),
        _mock_stratum_message(
            {
                "id": None,
                "method": "mining.set_extranonce",
                "params": ["aabbccdd", 1],
            }
        ),
        _mock_stratum_message({"id": 3, "result": True, "error": None}),
        _mock_mining_notify("job-2", "11" * 32, clean_jobs=False),
        _mock_stratum_message({"id": 4, "result": True, "error": None}),
    ]
    miner = MockStratumMiner(12345)
    searches_with_notifications = {1}
    notified_searches: set[int] = set()

    def select_readable(readers, _writers, _errors, timeout):
        if timeout == 0:
            search_count = find_nonce.call_count
            if (
                search_count in searches_with_notifications
                and search_count not in notified_searches
            ):
                notified_searches.add(search_count)
                return readers, [], []
            return [], [], []
        return readers, [], []

    with (
        patch(
            "test_framework.mock_miner.socket.create_connection",
            return_value=connection,
        ) as create_connection,
        patch(
            "test_framework.mock_miner.select.select",
            side_effect=select_readable,
        ),
        patch.object(
            miner, "_find_nonce", side_effect=["00000000", "00000001"]
        ) as find_nonce,
    ):
        with miner.session(timeout=1.0):
            first_job = miner.current_job
            first_result = miner.mine_current_job(timeout=1.0)
            assert_equal(first_result.job_id, "job-1")
            assert_equal(miner._extranonce1, "abcd")
            assert_equal(miner._extranonce2_size, 4)
            assert_equal(miner._pending_extranonce, ("aabbccdd", 1))

            difficulty, next_job = miner.wait_for_next_job(timeout=1.0)
            assert_equal(difficulty, 0.01)
            assert_equal(next_job["job_id"], "job-2")
            assert_equal(miner._extranonce1, "aabbccdd")
            assert_equal(miner._extranonce2_size, 1)

            second_result = miner.mine_current_job(timeout=1.0)
            assert_equal(second_result.job_id, "job-2")
            connection.close.assert_not_called()

    create_connection.assert_called_once()
    connection.close.assert_called_once()
    submissions = [
        json.loads(sent.args[0].decode("utf8"))
        for sent in connection.sendall.call_args_list
        if json.loads(sent.args[0].decode("utf8"))["method"] == "mining.submit"
    ]
    assert_equal(
        [submission["params"][1] for submission in submissions],
        [first_job["job_id"], next_job["job_id"]],
    )
    assert_equal(
        [submission["params"][2] for submission in submissions],
        ["00000000", "00"],
    )
    find_nonce.assert_has_calls(
        [
            call(
                first_job,
                "abcd",
                4,
                extranonce2=bytes.fromhex("00000000"),
                on_share=ANY,
            ),
            call(
                next_job,
                "aabbccdd",
                1,
                extranonce2=bytes.fromhex("00"),
                on_share=ANY,
            ),
        ]
    )


def test_mock_miner_discards_superseded_work_during_search() -> None:
    from test_framework.mock_miner import MockMinerStateError, MockStratumMiner

    connection = Mock()
    connection.recv.side_effect = [
        _mock_stratum_message({"id": 1, "result": [[], "abcd", 4], "error": None}),
        b"".join(
            [
                _mock_stratum_message({"id": 2, "result": True, "error": None}),
                _mock_stratum_message(
                    {
                        "id": None,
                        "method": "mining.set_difficulty",
                        "params": [0.01],
                    }
                ),
                _mock_mining_notify("job-1", "00" * 32),
            ]
        ),
        b"".join(
            [
                _mock_mining_notify(
                    "stale-job", "22" * 32, clean_jobs=False
                ),
                _mock_mining_notify("job-2", "11" * 32),
            ]
        ),
        _mock_stratum_message({"id": 3, "result": True, "error": None}),
    ]
    miner = MockStratumMiner(12345)
    searches_with_notifications = {1}
    notified_searches: set[int] = set()

    def select_readable(readers, _writers, _errors, timeout):
        if timeout == 0:
            search_count = find_nonce.call_count
            if (
                search_count in searches_with_notifications
                and search_count not in notified_searches
            ):
                notified_searches.add(search_count)
                return readers, [], []
            return [], [], []
        return readers, [], []

    with (
        patch(
            "test_framework.mock_miner.socket.create_connection",
            return_value=connection,
        ) as create_connection,
        patch(
            "test_framework.mock_miner.select.select",
            side_effect=select_readable,
        ),
        patch.object(
            miner, "_find_nonce", side_effect=["00000000", "00000001"]
        ) as find_nonce,
    ):
        with miner.session(timeout=1.0):
            first_job = miner.current_job
            try:
                miner.mine_current_job(timeout=1.0)
            except MockMinerStateError as exc:
                assert "superseded by clean_jobs" in str(exc)
            else:
                raise AssertionError("clean_jobs did not invalidate the current job")

            difficulty, next_job = miner.wait_for_next_job(timeout=1.0)
            assert_equal(difficulty, 0.01)
            assert_equal(next_job["job_id"], "job-2")
            assert_equal(next_job["prevhash"], "11" * 32)
            second_result = miner.mine_current_job(timeout=1.0)
            assert_equal(second_result.job_id, "job-2")

    create_connection.assert_called_once()
    connection.close.assert_called_once()
    submissions = [
        json.loads(sent.args[0].decode("utf8"))
        for sent in connection.sendall.call_args_list
        if json.loads(sent.args[0].decode("utf8"))["method"] == "mining.submit"
    ]
    assert_equal(
        [submission["params"][1] for submission in submissions], ["job-2"]
    )
    find_nonce.assert_has_calls(
        [
            call(
                first_job,
                "abcd",
                4,
                extranonce2=bytes.fromhex("00000000"),
                on_share=ANY,
            ),
            call(
                next_job,
                "abcd",
                4,
                extranonce2=bytes.fromhex("00000001"),
                on_share=ANY,
            ),
        ]
    )


def _peer_info_client(connected_by_call: list[int]) -> RpcClient:
    """RpcClient whose ``getpeerinfo`` replies with the real object shape.

    Each call pops the next ``connected`` value, repeating the last one.
    """

    def transport(_url: str, payload: bytes, _timeout: float, _auth: str | None = None) -> bytes:
        request = json.loads(payload.decode("utf8"))
        assert_equal(request["method"], "getpeerinfo")
        connected = connected_by_call.pop(0) if len(connected_by_call) > 1 else connected_by_call[0]
        reply = {
            "total_peers": connected,
            "connected": connected,
            "inbound": 0,
            "outbound": connected,
            "network_groups": 0,
            "avg_latency_ms": 0.0,
            "peers": [{}] * connected,
        }
        return json.dumps({"jsonrpc": "2.0", "id": request["id"], "result": reply}).encode("utf8")

    return RpcClient("127.0.0.1", 1234, retry_delay=0, transport=transport)


def test_wait_for_peers_returns_once_the_minimum_is_connected() -> None:
    client = _peer_info_client([0, 0, 1])
    client.wait_for_peers(1, timeout=1.0)
    # One connected peer must not satisfy a request for two.
    try:
        client.wait_for_peers(2, timeout=0.05)
    except AssertionError as exc:
        assert "Peer count never reached 2" in str(exc), str(exc)
    else:
        raise AssertionError("wait_for_peers(2) returned with 1 connected peer")

    # With no connected peers, even a minimum of 1 must time out.
    empty_client = _peer_info_client([0])
    try:
        empty_client.wait_for_peers(1, timeout=0.05)
    except AssertionError as exc:
        assert "Peer count never reached 1" in str(exc), str(exc)
    else:
        raise AssertionError("wait_for_peers(1) returned with 0 connected peers")


def test_find_binary_relative_path() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        binary = root / "node" / "src" / "test-node"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\n", encoding="utf8")
        binary.chmod(binary.stat().st_mode | stat.S_IXUSR)  # must be executable for find_binary
        original_env = os.environ.pop("BP_TEST_NODE_PATH", None)
        try:
            assert_equal(
                find_binary(
                    "test-node",
                    "BP_TEST_NODE_PATH",
                    ["node/src/test-node"],
                    repo_root=root,
                ),
                binary,
            )
        finally:
            if original_env is not None:
                os.environ["BP_TEST_NODE_PATH"] = original_env


def test_find_binary_missing_skips() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        try:
            find_binary("definitely-missing-bp-binary", "BP_MISSING_BINARY", [], repo_root=Path(tmp))
        except SkipTest:
            return
    raise AssertionError("missing binary did not raise SkipTest")


def test_cleanup_manager_lifo_order() -> None:
    """Callbacks must run in reverse registration order."""
    order: list[int] = []
    cm = CleanupManager()
    cm.register(lambda: order.append(1), name="first")
    cm.register(lambda: order.append(2), name="second")
    cm.register(lambda: order.append(3), name="third")
    cm.run_all()
    assert_equal(order, [3, 2, 1])


def test_cleanup_manager_exception_swallowing() -> None:
    """A failing callback must not prevent subsequent callbacks from running."""
    ran: list[str] = []

    def boom() -> None:
        raise RuntimeError("intentional failure")

    cm = CleanupManager()
    cm.register(lambda: ran.append("before"), name="before")
    cm.register(boom, name="boom")
    cm.register(lambda: ran.append("after"), name="after")
    cm.run_all()
    assert "before" in ran
    assert "after" in ran


def test_cleanup_manager_idempotent() -> None:
    """run_all() called twice must only execute callbacks once."""
    count: list[int] = [0]
    cm = CleanupManager()
    cm.register(lambda: count.__setitem__(0, count[0] + 1), name="counter")
    cm.run_all()
    cm.run_all()
    assert_equal(count[0], 1)


def test_cleanup_manager_managed_process() -> None:
    """managed_process must terminate a subprocess when run_all() is called."""
    with tempfile.TemporaryDirectory() as tmp:
        fake = Path(tmp) / "fake.py"
        fake.write_text(
            "import signal, time\n"
            "signal.signal(signal.SIGTERM, lambda *_: __import__('sys').exit(0))\n"
            "time.sleep(60)\n",
            encoding="utf8",
        )
        proc = subprocess.Popen([sys.executable, str(fake)], start_new_session=True)
        try:
            cm = CleanupManager()
            cm.managed_process(proc, name="fake_process")
            cm.run_all()
            wait_until(lambda: proc.poll() is not None, timeout=5.0, interval=0.05)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait(timeout=1.0)
        assert proc.returncode is not None


def test_cleanup_manager_register_after_run_is_noop() -> None:
    """Registering after run_all() must not re-trigger cleanup."""
    ran: list[int] = [0]
    cm = CleanupManager()
    cm.run_all()
    cm.register(lambda: ran.__setitem__(0, ran[0] + 1), name="late")
    cm.run_all()
    assert_equal(ran[0], 0)


def test_cleanup_manager_signal_restore() -> None:
    """Signal handlers must be restored to previous state after run_all."""
    import signal
    original = signal.getsignal(signal.SIGTERM)
    cm = CleanupManager()
    # Constructor is side-effect-free; handlers are installed explicitly.
    cm.install_signal_handlers()
    assert signal.getsignal(signal.SIGTERM) is not original
    cm.run_all()
    assert signal.getsignal(signal.SIGTERM) is original


def test_cleanup_manager_zombie_reap() -> None:
    """terminate_process_group must call wait(timeout=0) if SIGKILL times out."""
    import os
    from test_framework.cleanup_manager import terminate_process_group
    
    class FakeProcess:
        def __init__(self):
            self.pid = 999999
            self.returncode = None
            self.wait_calls = []
        def poll(self):
            return self.returncode
        def wait(self, timeout=None):
            self.wait_calls.append(timeout)
            raise subprocess.TimeoutExpired(cmd="fake", timeout=timeout)
            
    proc = FakeProcess()
    original_getpgid = os.getpgid
    original_killpg = os.killpg
    try:
        os.getpgid = lambda pid: 11111 if pid == 0 else 12345
        os.killpg = lambda pgid, sig: None
        terminate_process_group(
            proc,  # type: ignore
            name="fake_zombie",
            term_timeout=0.01,
            kill_timeout=0.01
        )
    finally:
        os.getpgid = original_getpgid
        os.killpg = original_killpg
        
    assert_equal(len(proc.wait_calls), 3)
    assert_equal(proc.wait_calls[0], 0.01)
    assert_equal(proc.wait_calls[1], 0.01)
    assert_equal(proc.wait_calls[2], 0)


def test_cleanup_manager_toctou_race() -> None:
    """terminate_process_group must re-poll after getpgid to avoid TOCTOU."""
    import os
    from test_framework.cleanup_manager import terminate_process_group
    
    class FakeProcess:
        def __init__(self):
            self.pid = 999999
            self.returncode = None
            self.poll_calls = 0
        def poll(self):
            self.poll_calls += 1
            if self.poll_calls == 1:
                return None
            return 0
            
    proc = FakeProcess()
    original_getpgid = os.getpgid
    original_killpg = os.killpg
    kill_called = False
    try:
        os.getpgid = lambda pid: 11111 if pid == 0 else 12345
        def mock_killpg(pgid, sig):
            nonlocal kill_called
            kill_called = True
            
        os.killpg = mock_killpg
        terminate_process_group(
            proc,  # type: ignore
            name="fake_toctou",
            term_timeout=0.01,
            kill_timeout=0.01
        )
    finally:
        os.getpgid = original_getpgid
        os.killpg = original_killpg
        
    assert_equal(proc.poll_calls, 2)
    assert not kill_called, "killpg should not be called if process died before second poll"


def test_bitcoin_node_args_construction() -> None:
    """Verify BitcoinNode.start() builds correct CLI args for regtest mode."""
    from test_framework.bitcoin_node import BitcoinNode
    from test_framework.network_config import NetworkConfig
    from test_framework.log_manager import LogManager
    from test_framework.cleanup_manager import CleanupManager
    from test_framework.port_pool import PortPool
    import tempfile
    
    with tempfile.TemporaryDirectory() as td:
        config = NetworkConfig(
            network="regtest",
            bitcoin_bin_path=Path("/mock/bitcoin-node"),
        )
        lm = LogManager(Path(td), "test")
        cm = CleanupManager()
        pp = PortPool(port_seed=0, validate_ports=False)
        
        node = BitcoinNode(config, Path(td), pp, cm, lm)
        node.binary_path = Path("/mock/bitcoin-node")
        
        # We don't actually start it, we just check what would be passed to Popen
        # To do this safely, we can mock subprocess.Popen
        import subprocess
        original_popen = subprocess.Popen
        captured_args = []
        
        def mock_popen(args, **kwargs):
            captured_args.extend(args)
            raise RuntimeError("Mock interrupted start")
            
        try:
            subprocess.Popen = mock_popen
            try:
                node.start()
            except RuntimeError as e:
                if str(e) != "Mock interrupted start":
                    raise
        finally:
            subprocess.Popen = original_popen
            
        assert "-regtest" in captured_args
        assert "-server=1" in captured_args
        assert "-listen=0" in captured_args
        assert f"-rpcport={node.rpc_port}" in captured_args
        # Phase 1: per-test IPC socket path must be present
        ipcbind_args = [a for a in captured_args if a.startswith("-ipcbind=unix:")]
        assert ipcbind_args, "-ipcbind=unix:<path> must be in bitcoind args"
        assert str(node.ipc_socket_path) in ipcbind_args[0], (
            f"ipc_socket_path {node.ipc_socket_path} not reflected in {ipcbind_args[0]}"
        )


def test_test_node_port_allocation() -> None:
    """Verify TestNode allocates rpc, p2p, stratum ports from the pool with correct offsets."""
    from test_framework.test_node import TestNode
    from test_framework.network_config import NetworkConfig
    from test_framework.log_manager import LogManager
    from test_framework.cleanup_manager import CleanupManager
    from test_framework.port_pool import PortPool
    import tempfile
    
    with tempfile.TemporaryDirectory() as td:
        config = NetworkConfig(braidpool_bin_path=Path("/mock/braidpool-node"))
        lm = LogManager(Path(td), "test")
        cm = CleanupManager()
        pp = PortPool(port_seed=0, validate_ports=False)
        
        node0 = TestNode(0, Path(td), config, pp, cm, lm)
        node1 = TestNode(1, Path(td), config, pp, cm, lm)
        
        assert_equal(node0.rpc_port, 16040)
        assert_equal(node1.rpc_port, 16041)
        assert_equal(node0.p2p_port, 16010)
        assert_equal(node1.p2p_port, 16011)
        assert_equal(node0.stratum_port, 16070)
        assert_equal(node1.stratum_port, 16071)


def test_test_node_addnode_extra_arg() -> None:
    """Verify NodeManager._start_braidpool_nodes passes --addnode to node 1+."""
    from test_framework.node_manager import NodeManager
    from test_framework.network_config import NetworkConfig
    from test_framework.log_manager import LogManager
    from test_framework.cleanup_manager import CleanupManager
    from test_framework.port_pool import PortPool
    import tempfile
    
    with tempfile.TemporaryDirectory() as td:
        config = NetworkConfig(num_braidpool_nodes=2)
        lm = LogManager(Path(td), "test")
        cm = CleanupManager()
        pp = PortPool(port_seed=0)
        
        nm = NodeManager(config, lm, cm, pp)
        
        class MockBitcoin:
            rpc_port = 18443
            rpc_user = "u"
            rpc_password = "p"
            ipc_socket_path = Path(td) / "bitcoin" / "bitcoin.sock"
        
        nm.bitcoin = MockBitcoin()
        
        # We need to mock TestNode to capture extra_args
        from test_framework import node_manager
        original_test_node = node_manager.TestNode
        all_extra_args: list = []
        
        class MockTestNode:
            def __init__(self, index, *args, **kwargs):
                self.index = index
                self.p2p_port = 1000 + index
            def start(self, extra_args):
                all_extra_args.append(list(extra_args))
            def wait_for_rpc_connection(self):
                pass
            def stop_node(self):
                pass
                
        try:
            node_manager.TestNode = MockTestNode
            nm._start_braidpool_nodes()
        finally:
            node_manager.TestNode = original_test_node
            
        assert_equal(len(all_extra_args), 2)
        assert not any(arg.startswith("--addnode=") for arg in all_extra_args[0])
        assert "--addnode=/ip4/127.0.0.1/udp/1000/quic-v1" in all_extra_args[1]  
        expected_ipc_arg = f"--ipc-socket={nm.bitcoin.ipc_socket_path}"
        for node_args in all_extra_args:
            assert expected_ipc_arg in node_args


def test_node_manager_skip_on_missing_binary() -> None:
    """Verify SkipTest is raised when find_braidpool_bin() fails."""
    from test_framework.test_node import find_braidpool_bin
    from test_framework.util import SkipTest
    original_env = os.environ.get("BRAIDPOOL_BIN_PATH")
    original_path = os.environ.get("PATH")
    try:
        os.environ["BRAIDPOOL_BIN_PATH"] = "/path/to/nowhere/nonexistent_bin"
        os.environ["PATH"] = str(Path("/path/to/nowhere"))
        try:
            find_braidpool_bin(repo_root=Path("/path/to/nowhere"))
            assert False, "Should have raised SkipTest"
        except SkipTest as e:
            assert "node not found" in str(e)
    finally:
        if original_env is not None:
            os.environ["BRAIDPOOL_BIN_PATH"] = original_env
        else:
            os.environ.pop("BRAIDPOOL_BIN_PATH", None)
        if original_path is not None:
            os.environ["PATH"] = original_path
        else:
            os.environ.pop("PATH", None)


def test_node_manager_teardown_order() -> None:
    """Verify teardown calls stop_node() on all nodes in reverse index order."""
    from test_framework.node_manager import NodeManager
    from test_framework.network_config import NetworkConfig
    from test_framework.log_manager import LogManager
    from test_framework.cleanup_manager import CleanupManager
    from test_framework.port_pool import PortPool
    import tempfile
    
    with tempfile.TemporaryDirectory() as td:
        config = NetworkConfig(num_braidpool_nodes=2)
        lm = LogManager(Path(td), "test")
        cm = CleanupManager()
        pp = PortPool(port_seed=0)
        
        nm = NodeManager(config, lm, cm, pp)
        
        stop_order = []
        
        class MockNode:
            def __init__(self, index):
                self.index = index
            def stop_node(self):
                stop_order.append(self.index)
                
        nm.nodes = [MockNode(0), MockNode(1)]
        
        class MockBitcoin:
            def stop(self):
                stop_order.append("bitcoin")
        nm.bitcoin = MockBitcoin()
        
        nm.teardown()
        
        assert_equal(stop_order, [1, 0, "bitcoin"])


def test_bitcoin_node_skip_on_missing_binary() -> None:
    """Verify SkipTest is raised when find_bitcoind() fails."""
    from test_framework.bitcoin_node import find_bitcoind
    from test_framework.util import SkipTest
    import os
    original_env = os.environ.get("BITCOIN_NODE_PATH")
    try:
        os.environ["BITCOIN_NODE_PATH"] = "/path/to/nowhere/nonexistent_bin"
        try:
            find_bitcoind(repo_root=Path("/path/to/nowhere"))
            assert False, "Should have raised SkipTest"
        except SkipTest as e:
            assert "bitcoin-node not found" in str(e)
    finally:
        if original_env is not None:
            os.environ["BITCOIN_NODE_PATH"] = original_env
        else:
            del os.environ["BITCOIN_NODE_PATH"]


TESTS = [
    test_network_config_defaults,
    test_port_pool_deterministic_band,
    test_port_seed_global_default,
    test_port_pool_auto_select_skips_ephemeral_range,
    test_port_pool_auto_select_skips_udp_occupied_p2p_port,
    test_port_pool_auto_select_stays_within_tcp_port_range,
    test_port_pool_manual_collision,
    test_port_pool_bind_failure_is_reported,
    test_port_pool_udp_bind_failure_is_reported,
    test_log_manager_paths_and_cleanup,
    test_log_manager_nocleanup,
    test_wait_until,
    test_runner_args_parsing,
    test_runner_args_unknown_passthrough,
    test_runner_stable_port_seeds,
    test_runner_default_selection_and_filters,
    test_runner_result_status_mapping,
    test_tail_file_reads_suffix,
    test_structured_logging_utils,
    test_rpc_client_success_and_wrapper_mapping,
    test_rpc_client_error_preserves_code_and_message,
    test_rpc_client_retries_connection_refused,
    test_rpc_client_transport_failure_after_retries,
    test_rpc_client_timeout,
    test_rpc_client_invalid_response,
    test_mock_miner_retries_early_eof,
    test_mock_miner_header_hash_fixture,
    test_mock_miner_returns_on_nbits,
    test_mock_miner_continues_after_share,
    test_mock_miner_rejects_share_submission,
    test_mock_miner_rejects_invalid_set_difficulty,
    test_mock_miner_rejects_authorization,
    test_mock_miner_rejects_unaccepted_submission,
    test_mock_miner_categorizes_stratum_request_errors,
    test_mock_miner_session_reuses_pushed_jobs,
    test_mock_miner_stages_extranonce_until_next_job,
    test_mock_miner_discards_superseded_work_during_search,
    test_wait_for_peers_returns_once_the_minimum_is_connected,
    test_find_binary_relative_path,
    test_find_binary_missing_skips,
    test_cleanup_manager_lifo_order,
    test_cleanup_manager_exception_swallowing,
    test_cleanup_manager_idempotent,
    test_cleanup_manager_managed_process,
    test_cleanup_manager_register_after_run_is_noop,
    test_cleanup_manager_signal_restore,
    test_cleanup_manager_zombie_reap,
    test_cleanup_manager_toctou_race,
    test_bitcoin_node_args_construction,
    test_test_node_port_allocation,
    test_test_node_addnode_extra_arg,
    test_node_manager_skip_on_missing_binary,
    test_node_manager_teardown_order,
    test_bitcoin_node_skip_on_missing_binary,
]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tmpdir", type=Path)
    parser.add_argument("--portseed", type=int, default=0)
    parser.add_argument("--nocleanup", action="store_true")
    args = parser.parse_args()

    # All test output goes through the structured logger so every line
    # carries a UTC timestamp, matching the rest of the framework.
    # Configure the root logger too so module-level loggers in rpc_client,
    # port_pool, util, etc. (which propagate=True by default) are also
    # captured with timestamps rather than falling through to Python's
    # default plain-text stderr handler.
    configure_stream_logger(None, level="WARNING")
    configure_stream_logger(__name__)
    log = logging.getLogger(__name__)

    failures = 0
    for test in TESTS:
        try:
            test()
            log_event(log, "test_passed", test=test.__name__)
        except Exception as exc:
            failures += 1
            log_event(log, "test_failed", level=logging.ERROR,
                      test=test.__name__, error=repr(exc))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
