# Braidpool Functional Test Framework Guide

Use this guide to write, run, and debug executable functional tests under
`tests/functional/`. The framework starts the requested Bitcoin, Braidpool,
and miner processes; assigns isolated ports; collects logs and timing; and
always attempts cleanup.

If you are in a hurry, read **Quick start**, **Running tests**, and **Things to
keep in mind**. Use the other sections as reference while writing a test.

## Quick start

1. Create `tests/functional/feature_<name>.py`.
2. Subclass `BraidpoolTestFramework`.
3. Implement `set_test_params()` and `run_test()`.
4. Run the file through `test_runner.py`.

```python
#!/usr/bin/env python3

from test_framework.network_config import NetworkConfig
from test_framework.test_framework import BraidpoolTestFramework
from test_framework.util import assert_equal


class FeatureNodeHealth(BraidpoolTestFramework):
    """Check that two nodes start and agree on their bead count."""

    def set_test_params(self) -> None:
        self.config = NetworkConfig(
            num_braidpool_nodes=2,
            num_cpu_miners=0,
            initial_blocks=101,
        )

    def run_test(self) -> None:
        assert_equal(len(self.nodes), 2)
        assert_equal(all(node.is_running() for node in self.nodes), True)

        self.sync_all()
        assert_equal(
            self.nodes[0].rpc.get_bead_count(),
            self.nodes[1].rpc.get_bead_count(),
        )


if __name__ == "__main__":
    FeatureNodeHealth(__file__).main()
```

From the repository root:

```bash
python3 tests/functional/test_runner.py feature_node_health.py
```

The base class owns `__init__()` and `main()`. Do not override them.

## Lifecycle and responsibilities

Every test follows the same lifecycle:

1. Parse framework and test-specific options.
2. Create the test directory and start its timing report.
3. Call `set_test_params()`.
4. Validate the configuration and initialize logging, cleanup, and ports.
5. Call `setup_network()` to start Bitcoin, Braidpool nodes, and miners.
6. Call `run_test()`.
7. Stop managed resources, run custom cleanup, finalize the report, and
   remove or preserve the test directory.

The shutdown phase runs after passes, skips, failures, and interruptions.

### Methods a test may implement

| Method | Required | Purpose |
|---|---:|---|
| `set_test_params()` | Yes | Assign the test's `NetworkConfig`. |
| `run_test()` | Yes | Make RPC calls and assertions after setup completes. |
| `add_options(parser)` | No | Add test-specific CLI options. |
| `setup_network()` | Rarely | Replace the default network startup completely. |

`set_test_params()` and `run_test()` must be declared on every concrete test
class. The framework rejects classes that omit them or override `__init__()`
or `main()`.

The default `setup_network()` calls `NodeManager.setup()`. Override it only
for a custom topology or a test that deliberately needs no external binaries.
Once overridden, the test owns all setup performed in that method.

## Configuring the test network

Assign a `NetworkConfig` in `set_test_params()`:

```python
def set_test_params(self) -> None:
    self.config = NetworkConfig(
        num_braidpool_nodes=3,
        num_cpu_miners=2,
        network="regtest",
        initial_blocks=101,
        random_seed=42,
    )
```

### NetworkConfig reference

| Field | Default | Meaning |
|---|---:|---|
| `num_braidpool_nodes` | `1` | Number of Braidpool nodes to start. |
| `num_cpu_miners` | `0` | Number of `minerd` processes, distributed across the nodes. |
| `network` | `"regtest"` | Bitcoin/Braidpool network: `regtest`, `cpunet`, or `signet`. |
| `initial_blocks` | `101` | Bitcoin blocks generated before Braidpool nodes start. |
| `bitcoin_rpc_port` | `None` | Manual Bitcoin RPC port; normally leave unset. |
| `bitcoin_p2p_port` | `None` | Manual Bitcoin P2P port; normally leave unset. |
| `bitcoin_ipc_socket` | `None` | Manual IPC socket; normally use the isolated per-test path. |
| `bitcoin_bin_path` | `None` | Explicit `bitcoin-node` path. |
| `braidpool_bin_path` | `None` | Explicit Braidpool node path. |
| `minerd_bin_path` | `None` | Explicit CPU miner path. |
| `startup_timeout_braidpool` | `30.0` | Braidpool startup timeout in seconds. |
| `startup_timeout_btc` | `90.0` | Bitcoin startup timeout in seconds. |
| `startup_timeout_minerd` | `60.0` | Miner startup timeout in seconds. |
| `rpc_timeout` | `10.0` | Timeout for one RPC call. |
| `peer_connection_timeout` | `15.0` | Peer connection timeout. |
| `bead_propagation_timeout` | `60.0` | Default `sync_all()` timeout. |
| `log_level` | `"INFO"` | Framework log level. |
| `random_seed` | `42` | Seed used by Python's global `random` module. |

Counts cannot be negative. Miners require at least one Braidpool node.

Avoid fixed ports and shared IPC sockets: they make parallel tests collide.
The runner assigns a stable `--portseed` to each script, and `PortPool` uses it
to create an isolated port band.

## Objects available in run_test()

After normal setup, the base class exposes:

| Attribute | Type/use |
|---|---|
| `self.bitcoin` | Managed `BitcoinNode`; use `self.bitcoin.rpc._call(...)`. |
| `self.nodes` | List of managed `TestNode` objects. |
| `self.miners` | List of managed `CpuMiner` objects. |
| `self.config` | Effective `NetworkConfig`, including CLI overrides. |
| `self.options` | Parsed framework and test-specific arguments. |
| `self.tmpdir` | This script's artifact directory. |
| `self.log` | Structured framework logger. |
| `self.cleanup_manager` | LIFO cleanup registry for custom resources. |
| `self.port_pool` | Isolated port allocator for extra services. |
| `self.report` | Timing report owned and finalized by the framework. |

The framework manages the lifecycle of `self.bitcoin`, `self.nodes`, and
`self.miners`. Tests should normally inspect them, not stop them manually.

### RPC calls

Use the typed Braidpool helpers where available:

```python
count = self.nodes[0].rpc.get_bead_count()
tips = self.nodes[0].rpc.get_tips()
info = self.nodes[0].rpc.get_braid_info()
```

`TestNode` also delegates unknown public attributes to its RPC client, so
`self.nodes[0].get_bead_count()` works. Using `.rpc` explicitly is clearer when
reading a test.

For Bitcoin RPC:

```python
chain = self.bitcoin.rpc._call("getblockchaininfo")
```

Unknown Braidpool RPC method names are dispatched dynamically. A typo therefore
becomes a server RPC failure rather than a local `AttributeError`; prefer the
defined helper methods.

The RPC client retries transient connection-refused and HTTP 503 failures.
Timeouts, authentication failures, malformed responses, and ordinary RPC
errors still fail the call.

## Assertions, waiting, synchronization, and skipping

Use the shared assertion helpers for useful failure messages:

```python
from test_framework.util import (
    assert_equal,
    assert_greater_than,
    assert_greater_than_or_equal,
)
```

Do not use fixed sleeps to wait for asynchronous state. Poll the condition:

```python
self.wait_until(
    lambda: self.nodes[0].rpc.get_bead_count() >= 5,
    timeout=30.0,
    message="node did not receive five beads",
)
```

`self.wait_until()` automatically applies `--timeout-factor`. It remembers the
last predicate exception and includes it if the wait expires.

Useful RPC polling helpers include:

```python
self.nodes[0].rpc.wait_for_ready(timeout=30.0)
count = self.nodes[0].rpc.wait_for_bead_count(5, timeout=60.0)
self.nodes[0].rpc.wait_for_peers(1, timeout=30.0)
```

Use `self.sync_all()` to wait until all Braidpool nodes report the same bead
count. It checks counts, not complete DAG equality. An explicit
`self.sync_all(timeout=...)` value and the configured
`bead_propagation_timeout` default are both expressed in unscaled seconds;
`--timeout-factor` is applied exactly once by `sync_all()`.

Skip when a required runtime capability is unavailable:

```python
if not capability_available:
    self.skip_test("requires capability X")
```

Missing binaries are skipped automatically. Do not catch an unexpected
exception just to turn it into a skip.

## Test-specific options

Add options without replacing the framework parser:

```python
import argparse

def add_options(self, parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--expected-beads", type=int, default=5)

def run_test(self) -> None:
    self.nodes[0].rpc.wait_for_bead_count(self.options.expected_beads)
```

Run it directly:

```bash
python3 tests/functional/feature_example.py --expected-beads=10
```

Or through the runner; unrecognized runner options are forwarded to the test:

```bash
python3 tests/functional/test_runner.py feature_example.py --expected-beads=10
```

When several scripts are selected, a forwarded option is passed to all of
them. Use it only when every selected script accepts it. Pass option-style
arguments directly as shown; a separate `--` delimiter is not needed.

## Custom resources and cleanup

Framework-created processes are registered automatically. Register every
additional long-lived resource as soon as it is created:

```python
def setup_network(self) -> None:
    super().setup_network()
    self.helper = start_helper()
    self.cleanup_manager.register(self.helper.close, name="helper")
```

Callbacks run exactly once in last-in, first-out order. One callback failure is
logged and does not prevent later callbacks from running.

For a custom subprocess, start a new session and register the process group:

```python
process = subprocess.Popen(command, start_new_session=True)
self.cleanup_manager.managed_process(process, name="custom-helper")
```

Register immediately after creation, before another operation can raise. Do not
duplicate process termination logic or rely on garbage collection. Use context
managers for ordinary files and short-lived resources.

`CleanupManager` installs `atexit`, `SIGINT`, and `SIGTERM` hooks in the actual
framework lifecycle. A low-level unit test may create `CleanupManager()` without
installing those global hooks and call `run_all()` directly.

## Writing a no-binary framework test

The default network setup always starts Bitcoin first. For a framework-only
test, configure zero processes and override `setup_network()`:

```python
class FeatureNoBinaries(BraidpoolTestFramework):
    def set_test_params(self) -> None:
        self.config = NetworkConfig(
            num_braidpool_nodes=0,
            num_cpu_miners=0,
            initial_blocks=0,
        )

    def setup_network(self) -> None:
        pass

    def run_test(self) -> None:
        assert_equal(self.nodes, [])
```

See [`feature_framework_lifecycle.py`](../feature_framework_lifecycle.py) for a
complete example with custom options, polling, logging, and cleanup callbacks.

## Binaries and discovery

A normal network test needs `bitcoin-node`; tests with Braidpool nodes also need
the Braidpool binary, and miner tests need `minerd`.

```bash
# Build the Braidpool node from the repository root.
cargo build --bin node
```

Binary selection uses this order:

1. A path supplied by a test configuration or CLI option.
2. The component's environment variable.
3. Known paths relative to the repository root.
4. The executable found on `PATH`.

| Component | CLI option | Environment variable | Common relative path |
|---|---|---|---|
| Braidpool node | `--braidpool-bin` | `BRAIDPOOL_BIN_PATH` | `target/debug/node` |
| Bitcoin node | `--bitcoin-bin` | `BITCOIN_NODE_PATH` | `../bitcoin/build/bin/bitcoin-node` |
| CPU miner | `--minerd-bin` | `MINERD_PATH` | `node/src/cpuminer/minerd` |

Example:

```bash
export BRAIDPOOL_BIN_PATH="$PWD/target/debug/node"
export BITCOIN_NODE_PATH="$PWD/../bitcoin/build/bin/bitcoin-node"
python3 tests/functional/test_runner.py feature_node_health.py
```

Paths are resolved from the framework's location, not the caller's current
directory.

## Running tests

All commands below assume the repository root.

### Direct execution

```bash
python3 tests/functional/feature_example.py
```

Direct execution is useful for `--pdbonfailure`. If direct tests run in
parallel, give each one a unique `--portseed`.

### Test runner

```bash
# Run every script registered in BASE_SCRIPTS.
python3 tests/functional/test_runner.py

# Run one or more named scripts.
python3 tests/functional/test_runner.py feature_a.py feature_b.py

# Run up to four scripts concurrently.
python3 tests/functional/test_runner.py --jobs=4

# Keep artifacts from successful scripts.
python3 tests/functional/test_runner.py --nocleanup feature_a.py
```

To include a new script in the default suite, add its filename to
`BASE_SCRIPTS` in [`test_runner.py`](../test_runner.py). Put expensive or
optional integration scripts in `EXTENDED_SCRIPTS`; they run when
`--extended` is supplied.

### Runner options

| Option | Purpose |
|---|---|
| `SCRIPT...` | Run the named scripts; `.py` is optional. |
| `--jobs=N`, `-j N` | Maximum scripts running concurrently. |
| `--timeout=SECONDS` | Hard limit per script; `0` disables it. |
| `--failfast`, `-F` | Stop scheduling after a failure is observed. |
| `--filter=REGEX` | Keep registered/selected tests matching a regex. |
| `--exclude=A,B`, `-x A,B` | Exclude comma-separated script names. |
| `--extended` | Add scripts registered in `EXTENDED_SCRIPTS`. |
| `--nocleanup` | Preserve artifacts for successful tests too. |
| `--combinedlogslen=N`, `-c N` | Print the final N stdout/stderr lines on failure. |
| `--resultsfile=PATH`, `-r PATH` | Write a CSV result summary. |
| `--tmpdirprefix=PATH`, `-t PATH` | Parent directory for the runner's artifacts. |

`--timeout` belongs to the runner and can terminate a whole script.
`--timeout-factor` belongs to the framework and scales its internal startup,
RPC, peer, propagation, and `self.wait_until()` timeouts.

### Framework options

These options are available during direct execution. The runner forwards the
applicable options to each child script:

| Option | Purpose |
|---|---|
| `--tmpdir=PATH` | Use an explicit per-test artifact directory. |
| `--nocleanup` | Preserve artifacts after pass or skip. |
| `--loglevel=LEVEL` | Override the configured log level. |
| `--tracerpc` | Add RPC request tracing to the framework log. |
| `--portseed=N` | Select the deterministic port band; must be non-negative. |
| `--randomseed=N` | Override `NetworkConfig.random_seed`. |
| `--timeout-factor=N` | Multiply framework timeouts; must be positive. |
| `--pdbonfailure` | Enter post-mortem debugging after a test exception. |
| `--network=NAME` | Override the configured network. |
| `--braidpool-bin=PATH` | Override the Braidpool node binary. |
| `--bitcoin-bin=PATH` | Override the Bitcoin node binary. |
| `--minerd-bin=PATH` | Override the CPU miner binary. |

`--cachedir` and `--configfile` are currently reserved; do not rely on them to
change framework behavior.

The runner owns each child's `--tmpdir` and `--portseed` so concurrent scripts
remain isolated. Values supplied for those two options through the runner are
overridden; use them only when executing a script directly. `--pdbonfailure`
is also most useful during direct execution in an interactive terminal.

### Exit codes

| Code | Meaning |
|---:|---|
| `0` | Passed. |
| `1` | Failed. |
| `77` | Skipped; the runner treats this as successful. |

The runner itself returns `0` when all results are passed or skipped, otherwise
`1`.

## Artifacts and reports

Failed tests are always preserved. Passed and skipped tests are removed unless
`--nocleanup` is used.

```text
/tmp/bp_func_test_runner_<timestamp>_<suffix>/
└── feature_example_0/
    ├── stdout.log
    ├── stderr.log
    ├── test_framework.log
    ├── reports/
    │   └── summary.json
    ├── bitcoin/
    │   ├── stdout.log
    │   └── stderr.log
    ├── node0/
    │   ├── stdout.log
    │   └── stderr.log
    └── miner0/
        ├── stdout.log
        └── stderr.log
```

`test_framework.log` contains one structured JSON event per line. Component
directories contain the raw process output. Combine a preserved run's logs with:

```bash
python3 tests/functional/combine_logs.py /tmp/bp_func_test_runner_.../feature_example_0
```

The timing report currently contains only identity, status, start, end, and
total runtime:

```json
{
  "end_time": "2026-08-13T10:00:03.250+00:00",
  "run_id": "feature_example-feature_example_0",
  "start_time": "2026-08-13T10:00:00.000+00:00",
  "status": "passed",
  "test_name": "feature_example",
  "total_time_seconds": 3.25
}
```

Do not write or finalize this report from the test. The framework writes it
atomically during shutdown; the runner supplies a failed fallback report if a
timed-out or abruptly terminated child cannot finalize its own report.

## Debugging failures

1. Re-run only the failing script with `--nocleanup`.
2. Add `--loglevel=DEBUG --tracerpc` when RPC flow matters.
3. Use `--combinedlogslen=100` for immediate runner output.
4. Inspect `stderr.log`, then `test_framework.log`, then component logs.
5. Increase `--timeout-factor` only if the operation is legitimately slow.

```bash
python3 tests/functional/test_runner.py \
  --nocleanup \
  --combinedlogslen=100 \
  feature_example.py \
  --loglevel=DEBUG \
  --tracerpc
```

Useful framework events include:

| Event | Meaning |
|---|---|
| `test_failed` | The test body or setup raised an exception. |
| `test_skipped` | The test deliberately skipped. |
| `rpc_retry` / `rpc_timeout` | RPC transport retry or timeout. |
| `cleanup_callback_failed` | One cleanup callback failed; others continue. |
| `cleanup_signal_received` | SIGINT or SIGTERM initiated cleanup. |
| `process_signal_sent` | A managed process received SIGTERM or SIGKILL. |
| `process_group_is_self` | A subprocess was not isolated safely. |
| `log_cleanup_failed` | Successful-run artifact deletion failed. |

## Things to keep in mind

- Keep one scenario per script and use descriptive `feature_*.py` names.
- Never override `__init__()` or `main()`.
- Prefer the default network setup; override it only with a clear reason.
- Use `self.wait_until()` instead of `time.sleep()` for asynchronous state.
- Use deterministic seeds and framework-allocated ports.
- Register custom resources immediately and start subprocesses with
  `start_new_session=True`.
- Let the framework stop its own nodes and miners.
- Preserve artifacts with `--nocleanup`; there is no separate log-retention
  option.
- Avoid secrets in arguments and logs. RPC tracing is for controlled test data.
- Do not assume `sync_all()` proves complete DAG equivalence.
- Keep tests bounded so runner timeouts can diagnose a real hang.
- A cleanup callback exception is logged but does not stop the remaining
  callbacks; inspect cleanup errors even when the test body passed.

## Pre-submit checklist

- The script implements `set_test_params()` and `run_test()`.
- Process counts, block count, network, and timeouts are explicit where relevant.
- Assertions test observable behavior, not only successful startup.
- Asynchronous assertions use bounded polling.
- Custom processes and resources are registered for cleanup.
- No fixed port or shared IPC path breaks parallel execution.
- The test passes directly and through `test_runner.py`.
- The test passes with `--jobs` alongside another network test.
- Failure output is understandable from preserved logs.
- The script is added to `BASE_SCRIPTS` or `EXTENDED_SCRIPTS` when appropriate.

For a shorter command-only reference, see
[`running_tests.md`](running_tests.md). For framework internals and lessons from
past bugs, see [`learnings.md`](learnings.md).
