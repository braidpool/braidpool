#!/usr/bin/env python3
"""Self-tests for the Braidpool functional test framework (Phases 1–3)."""

from __future__ import annotations

import argparse
import json
import logging
import subprocess
import stat
import sys
import tempfile
from pathlib import Path

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
from test_framework.miner_manager import CpuMiner, find_minerd
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
    assert_equal(cfg.num_cpu_miners, 0)
    assert_equal(cfg.network, "regtest")
    assert_equal(cfg.initial_blocks, 101)
    assert cfg.bitcoin_rpc_port is None
    assert cfg.bitcoin_p2p_port is None
    assert cfg.bitcoin_ipc_socket is None
    assert cfg.bitcoin_bin_path is None
    assert cfg.braidpool_bin_path is None
    assert cfg.minerd_bin_path is None
    assert_equal(cfg.startup_timeout_braidpool, 30.0)
    assert_equal(cfg.startup_timeout_btc, 90.0)
    assert_equal(cfg.startup_timeout_minerd, 60.0)
    assert_equal(cfg.rpc_timeout, 10.0)
    assert_equal(cfg.peer_connection_timeout, 15.0)
    assert_equal(cfg.bead_propagation_timeout, 60.0)
    assert_equal(cfg.log_level, "INFO")
    assert not cfg.keep_logs_on_success
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
    scheduled = schedule_tests(["a.py", "b.py --arg", "c.py"])
    assert_equal([item.port_seed for item in scheduled], [0, 1, 2])
    assert_equal([item.command for item in scheduled], ["a.py", "b.py --arg", "c.py"])


def test_runner_default_selection_and_filters() -> None:
    expected = ["feature_framework_unit_tests.py", "feature_node_startup.py"]
    assert_equal(build_test_list([], extended=False, exclude=None, pattern=None), expected)
    assert_equal(
        build_test_list([], extended=False, exclude="feature_node_startup", pattern=None),
        ["feature_framework_unit_tests.py"],
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


def test_miner_log_parsing() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        miner = CpuMiner(3333, Path(tmp), minerd_path="unused")
        miner.stdout_path.write_text(
            "accepted: 1/1\nshare accepted\nrejected share\n",
            encoding="utf8",
        )
        miner.stderr_path.write_text("Accepted share from worker\n", encoding="utf8")
        assert_equal(miner.shares_submitted(), 3)


def test_find_binary_relative_path() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        binary = root / "node" / "src" / "cpuminer" / "minerd"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\n", encoding="utf8")
        binary.chmod(binary.stat().st_mode | stat.S_IXUSR)  # must be executable for find_binary
        assert_equal(find_minerd(repo_root=root), binary)


def test_find_binary_missing_skips() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        try:
            find_binary("definitely-missing-bp-binary", "BP_MISSING_BINARY", [], repo_root=Path(tmp))
        except SkipTest:
            return
    raise AssertionError("missing binary did not raise SkipTest")


def test_cpu_miner_fake_process_lifecycle() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        fake_minerd = root / "fake_minerd.py"
        fake_minerd.write_text(
            "#!/usr/bin/env python3\n"
            "import signal\n"
            "import sys\n"
            "import time\n"
            "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))\n"
            "print('fake miner started', flush=True)\n"
            "time.sleep(60)\n",
            encoding="utf8",
        )
        fake_minerd.chmod(fake_minerd.stat().st_mode | stat.S_IXUSR)
        miner = CpuMiner(3333, root / "miner", minerd_path=fake_minerd)
        miner.start()
        try:
            wait_until(miner.is_alive, timeout=2.0, interval=0.01)
        finally:
            miner.stop(term_timeout=0.5, kill_timeout=0.5)
        wait_until(lambda: not miner.is_alive(), timeout=2.0, interval=0.01)
        assert (root / "miner" / STDOUT_LOG_NAME).exists()
        assert (root / "miner" / STDERR_LOG_NAME).exists()


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
        assert "--addnode=127.0.0.1:1000" in all_extra_args[1]
        expected_ipc_arg = f"--ipc-socket={nm.bitcoin.ipc_socket_path}"
        for node_args in all_extra_args:
            assert expected_ipc_arg in node_args


def test_node_manager_skip_on_missing_binary() -> None:
    """Verify SkipTest is raised when find_braidpool_bin() fails."""
    from test_framework.test_node import find_braidpool_bin
    from test_framework.util import SkipTest
    import os
    original_env = os.environ.get("BRAIDPOOL_BIN_PATH")
    try:
        os.environ["BRAIDPOOL_BIN_PATH"] = "/path/to/nowhere/nonexistent_bin"
        try:
            find_braidpool_bin(repo_root=Path("/path/to/nowhere"))
            assert False, "Should have raised SkipTest"
        except SkipTest as e:
            assert "braidpool-node not found" in str(e)
    finally:
        if original_env is not None:
            os.environ["BRAIDPOOL_BIN_PATH"] = original_env
        else:
            del os.environ["BRAIDPOOL_BIN_PATH"]


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
    test_port_pool_manual_collision,
    test_port_pool_bind_failure_is_reported,
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
    test_miner_log_parsing,
    test_find_binary_relative_path,
    test_find_binary_missing_skips,
    test_cpu_miner_fake_process_lifecycle,
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
