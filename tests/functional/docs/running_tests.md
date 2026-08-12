# Running the Functional Test Suite

This guide explains how to run both the framework self-tests and the node-startup integration test.


## 2. Unit Tests — No Binaries Required

`feature_framework_unit_tests.py` is entirely self-contained. All 38 tests run in-process using mocks and temporary directories.

### Run directly

```bash
cd tests/functional
python3 feature_framework_unit_tests.py
# Exit 0 = all passed.  Exit 1 = at least one failure.
```

### Run via the test runner

```bash
cd tests/functional
python3 test_runner.py feature_framework_unit_tests.py
```

### Scan for failures

```bash
python3 feature_framework_unit_tests.py 2>&1 | grep '"test_failed"'
# Silent = all green
```

### Count pass/fail

```bash
python3 feature_framework_unit_tests.py 2>&1 | \
  python3 -c "
import sys, json
p = f = 0
for l in sys.stdin:
    l = l.strip()
    if not l.startswith('{'): continue
    ev = json.loads(l).get('event','')
    if ev == 'test_passed': p += 1
    elif ev == 'test_failed': f += 1
print(f'{p} passed, {f} failed')
"
```

---

## 3. Integration Test — Requires Real Binaries

`feature_node_startup.py` starts a real `bitcoin-node` (regtest), mines 101 blocks, starts 2
`braidpool-node` instances, and verifies RPC health and sync.

**If binaries are absent, the test is automatically skipped (not failed).**

### Step 1 — Build braidpool-node

```bash
# From the repository root:
cargo build --bin node
# → target/debug/node
```

### Step 2 — Build bitcoin-node

```bash
# Clone Bitcoin Core adjacent to braidpool/ if not already done:
cd ..
git clone https://github.com/bitcoin/bitcoin.git
cd bitcoin
cmake -B build -DBUILD_UTIL_CHAINSTATE=OFF
cmake --build build -j$(nproc) --target bitcoin-node bitcoin-cli
# → build/bin/bitcoin-node, build/bin/bitcoin-cli
cd ../braidpool
```

### Step 3 — Tell the framework where the binaries are

**Option A — Environment variables (recommended for CI)**

```bash

# These paths are according to the paths stated above, if it is something els, then define accordingly:
export BRAIDPOOL_BIN_PATH=$(pwd)/target/debug/node
export BITCOIN_NODE_PATH=$(pwd)/../bitcoin/build/bin/bitcoin-node
export BITCOIN_CLI_PATH=$(pwd)/../bitcoin/build/bin/bitcoin-cli
```

**Option B — CLI flags (recommended for one-off runs)**

```bash
cd tests/functional
python3 feature_node_startup.py \
  --braidpool-bin ../../target/debug/node \
  --bitcoin-bin   ../../bitcoin/build/bin/bitcoin-node \
  --bitcoin-cli   ../../bitcoin/build/bin/bitcoin-cli
```

### Step 4 — Run via test runner

```bash
cd tests/functional
python3 test_runner.py feature_node_startup.py --combinedlogslen=50
# --combinedlogslen=50 prints the last 50 log lines on failure
```

### Step 5 — Run the full suite

```bash
cd tests/functional
python3 test_runner.py          # unit tests + integration test (sequential)
python3 test_runner.py --jobs=2 # parallel (safe; each test gets its own port band)
```

---

## 4. Inspecting Logs After a Run

When a test fails, logs are kept in a temp directory printed at the bottom of the output:
`Test data left in /tmp/bp_func_test_runner_YYYYMMDD_HHMMSS_.../`

```
/tmp/bp_func_test_runner_<timestamp>/
  feature_node_startup_0/
    test_framework.log      ← structured JSON events
    bitcoin/
      stdout.log            ← bitcoin-node stdout
      stderr.log            ← bitcoin-node stderr
    node0/
      stdout.log            ← braidpool node 0 stdout
      stderr.log            ← braidpool node 0 stderr
    node1/
      stdout.log            ← braidpool node 1 stdout
      stderr.log            ← braidpool node 1 stderr
```

Useful one-liners:

```bash
# Pretty-print framework log
cat /tmp/bp_func_test_runner_*/feature_node_startup_0/test_framework.log | \
  python3 -c "import sys,json; [print(json.dumps(json.loads(l), indent=2)) for l in sys.stdin if l.strip()]"

# Tail node 0 stderr
tail -50 /tmp/bp_func_test_runner_*/feature_node_startup_0/node0/stderr.log

# Keep all logs even on success (for debugging)
python3 test_runner.py --nocleanup
```

---

## 5. Binary Finding Logic

The framework resolves binaries in three layers, in order:

| Priority | Source | How to override |
|----------|--------|-----------------|
| 1 | `$ENV_VAR` (e.g. `$BRAIDPOOL_BIN_PATH`) | `export BRAIDPOOL_BIN_PATH=/path/to/node` |
| 2 | Relative paths from repo root | Automatically searched; see table below |
| 3 | `PATH` (system-wide install) | `sudo install target/debug/node /usr/local/bin/braidpool-node` |

If all three fail, `SkipTest` is raised and the test is marked **Skipped** (exit code 77), not Failed.

**Relative paths searched automatically (no config needed if you build in-tree):**

| Binary | Paths tried |
|--------|-------------|
| `braidpool-node` | `target/debug/node`, `target/release/node`, `node` |
| `bitcoin-node` | `../bitcoin/build/bin/bitcoin-node`, `bitcoin-node`, `target/debug/bitcoin-node` |
| `bitcoin-cli` | `../bitcoin/build/bin/bitcoin-cli`, `bitcoin-cli`, `target/debug/bitcoin-cli` |
| `minerd` | `node/src/cpuminer/minerd` |

> **Note:** The framework always resolves repo root from its own file location
> (`Path(__file__).resolve().parents[3]`), never from `cwd`. This means all paths work
> correctly regardless of where you invoke `test_runner.py` from.

---

## 6. Expected Exit Codes

| Exit code | Meaning |
|-----------|---------|
| `0` | All tests passed |
| `1` | At least one test failed |
| `77` | Test skipped (missing binary) — counted as passing by the runner |
