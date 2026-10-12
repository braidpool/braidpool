# Running Braidpool Functional Tests

This is the quick command reference. See the
[`Functional Test Framework Guide`](FRAMEWORK_GUIDE.md) for writing tests,
configuration, lifecycle details, cleanup rules, artifacts, and debugging.

Run commands from the repository root.

## Common commands

```bash
# Run scripts registered in test_runner.py's BASE_SCRIPTS.
python3 tests/functional/test_runner.py

# Run one script.
python3 tests/functional/test_runner.py feature_framework_lifecycle.py

# Run selected scripts in parallel.
python3 tests/functional/test_runner.py --jobs=4 feature_a.py feature_b.py

# Include scripts registered in EXTENDED_SCRIPTS.
python3 tests/functional/test_runner.py --extended

# Preserve artifacts and print the last 100 stdout/stderr lines on failure.
python3 tests/functional/test_runner.py \
  --nocleanup \
  --combinedlogslen=100 \
  feature_framework_lifecycle.py

# Apply a test-specific option; unknown runner options are forwarded.
python3 tests/functional/test_runner.py \
  feature_framework_lifecycle.py \
  --scenario=pass

# Run a script directly.
python3 tests/functional/feature_framework_lifecycle.py --nocleanup
```

## Useful runner options

| Option | Purpose |
|---|---|
| `--jobs=N` | Run at most N scripts concurrently. |
| `--timeout=SECONDS` | Hard timeout for each script; `0` disables it. |
| `--failfast` | Stop scheduling after a failure is observed. |
| `--filter=REGEX` | Keep test names matching a regex. |
| `--exclude=A,B` | Exclude comma-separated script names. |
| `--extended` | Include `EXTENDED_SCRIPTS`. |
| `--nocleanup` | Preserve successful and skipped test artifacts. |
| `--combinedlogslen=N` | Print N trailing stdout/stderr lines on failure. |
| `--resultsfile=PATH` | Write a CSV summary. |
| `--tmpdirprefix=PATH` | Choose the artifact parent directory. |

Use `--timeout-factor=N` to scale internal framework timeouts; it is different
from the runner's hard `--timeout`.

## Binary overrides

```bash
export BRAIDPOOL_BIN_PATH="$PWD/target/debug/node"
export BITCOIN_NODE_PATH="$PWD/../bitcoin/build/bin/bitcoin-node"
export MINERD_PATH="$PWD/node/src/cpuminer/minerd"
```

Equivalent per-test options are `--braidpool-bin`, `--bitcoin-bin`, and
`--minerd-bin`. Missing required binaries cause a skip (exit `77`), not a
failure.

## Results and artifacts

| Exit code | Meaning |
|---:|---|
| `0` | Passed, or every runner result passed/skipped. |
| `1` | Failed. |
| `77` | Direct script skipped. |

Failed runs are preserved under
`/tmp/bp_func_test_runner_<timestamp>_<suffix>/`. Successful runs are removed
unless `--nocleanup` is supplied. Each preserved test directory contains
`test_framework.log`, `stdout.log`, `stderr.log`, component logs, and
`reports/summary.json`.

```bash
python3 tests/functional/combine_logs.py \
  /tmp/bp_func_test_runner_.../feature_framework_lifecycle_0
```
