# Braidpool Stratum Load Testing

JMeter-based load tests for the braidpool stratum server. Tests concurrent miner connections, mining job dispatch latency, and share submission throughput.

## Prerequisites

1. **Bitcoin Core** with IPC support (`-ipcbind` flag, v28+ multiprocess build)
2. **Braidpool node** binary — build with `cargo build --release` from `node/`
3. **Apache JMeter** 5.6+ — [download](https://jmeter.apache.org/download_jmeter.cgi)
4. **netcat** (`nc`) for port-ready checks

Binaries are looked up in `PATH` by default. If yours live elsewhere, point
the scripts at them via environment variables:

```bash
export BITCOIN_NODE_BIN=$HOME/bitcoin/build/bin/bitcoin-node  # or bitcoind
export BITCOIN_CLI_BIN=$HOME/bitcoin/build/bin/bitcoin-cli
export BRAIDPOOL_BIN=$HOME/braidpool/target/release/node      # default: target/release, then target/debug
export JMETER_BIN=/opt/jmeter/bin/jmeter
```

## Quick Start

```bash
# Full automated run: setup → test → report → teardown
./scripts/run-tests.sh

# Or run a specific test plan
./scripts/run-tests.sh stratum-connection-stress
```

The HTML report is generated at `reports/<test>-<timestamp>-dashboard/index.html`.

## Manual Usage

### 1. Setup the test environment

```bash
./scripts/setup-regtest.sh
```

This starts bitcoind in regtest mode, creates a wallet, generates 101 blocks, starts the braidpool node, and begins periodic block generation (every 10s).

### 2. Run JMeter tests

```bash
# Full miner lifecycle (subscribe → authorize → submit loop)
jmeter -n \
  -t jmeter/stratum-load-test.jmx \
  -l reports/results.jtl \
  -Jtest.data.dir=data \
  -Jtest.lib.dir=lib

# Connection storm (rapid subscribe-only)
jmeter -n \
  -t jmeter/stratum-connection-stress.jmx \
  -l reports/stress-results.jtl
```

### 3. Generate HTML dashboard

```bash
jmeter -g reports/results.jtl -o reports/dashboard/
open reports/dashboard/index.html
```

### 4. Teardown

```bash
./scripts/teardown.sh
```

## Test Plans

### `stratum-load-test.jmx` — Full Miner Lifecycle

Simulates real miners through the complete stratum protocol:

1. TCP connect to stratum server
2. `mining.subscribe` — get extranonce1
3. `mining.configure` — negotiate version-rolling
4. `mining.authorize` — authenticate worker
5. Wait for `mining.notify` — receive block template
6. `mining.submit` loop — submit shares with random nonces (and rolled version bits, since version-rolling is negotiated in step 3 the server requires the 6th `version_bits` param)

Each thread uses a unique worker name from `data/miner-credentials.csv`.

**Configurable variables** (override with `-J` flags):

| Variable | Default | Description |
|----------|---------|-------------|
| `STRATUM_HOST` | `localhost` | Stratum server host |
| `STRATUM_PORT` | `3333` | Stratum server port |
| `NUM_MINERS` | `100` | Concurrent miner threads (max 1000 unique workers — the CSV recycles beyond that, reusing worker names) |
| `RAMP_UP_SECONDS` | `30` | Thread ramp-up period |
| `TEST_DURATION_SECONDS` | `300` | Submit loop duration per miner |
| `SUBMIT_INTERVAL_MS` | `1000` | Delay between submits per miner |

Example: 500 miners, 60s test, 500ms between submits:
```bash
jmeter -n \
  -t jmeter/stratum-load-test.jmx \
  -l reports/results.jtl \
  -Jtest.data.dir=data \
  -Jtest.lib.dir=lib \
  -JNUM_MINERS=500 \
  -JTEST_DURATION_SECONDS=60 \
  -JSUBMIT_INTERVAL_MS=500
```

### `stratum-connection-stress.jmx` — Connection Storm

Rapidly opens TCP connections and sends `mining.subscribe` to measure:
- Connection establishment rate
- Subscribe response latency under high connection churn
- Error rate when connections are exhausted

| Variable | Default | Description |
|----------|---------|-------------|
| `STRATUM_HOST` | `localhost` | Stratum server host |
| `STRATUM_PORT` | `3333` | Stratum server port |
| `NUM_CONNECTIONS` | `500` | Total connections to open |
| `RAMP_UP_SECONDS` | `10` | Ramp-up period |

## Environment Variables

Override defaults for the setup/teardown scripts:

| Variable | Default | Description |
|----------|---------|-------------|
| `BITCOIN_DATADIR` | `/tmp/braidpool-loadtest-bitcoin` | Bitcoin Core data directory |
| `IPC_SOCKET` | `/tmp/bitcoin-loadtest-regtest.sock` | IPC socket path |
| `RPC_USER` | `loadtest` | Bitcoin RPC username |
| `RPC_PASS` | `loadtest` | Bitcoin RPC password |
| `BITCOIN_RPC_PORT` | `18443` | Bitcoin RPC port |
| `STRATUM_PORT` | `3333` | Stratum server port |
| `BLOCK_INTERVAL` | `10` | Seconds between generated blocks |
| `NETWORK` | `regtest` | Bitcoin network |
| `BITCOIN_NODE_BIN` | `bitcoin-node`/`bitcoind` from PATH | Bitcoin Core daemon binary (multiprocess, v28+) |
| `BITCOIN_CLI_BIN` | `bitcoin-cli` from PATH | Bitcoin Core CLI binary |
| `BRAIDPOOL_BIN` | `target/release/node`, then `target/debug/node` | Braidpool node binary |
| `JMETER_BIN` | `jmeter` from PATH | JMeter launcher (run-tests.sh) |

## Directory Structure

```
load-testing/
├── README.md                  # This file
├── jmeter/
│   ├── stratum-load-test.jmx          # Full miner lifecycle test
│   └── stratum-connection-stress.jmx  # Connection storm test
├── scripts/
│   ├── setup-regtest.sh       # Start test environment
│   ├── generate-blocks.sh     # Background block generator
│   ├── teardown.sh            # Stop everything
│   └── run-tests.sh           # Automated orchestrator
├── data/
│   └── miner-credentials.csv  # 1000 unique worker names
├── lib/
│   └── stratum-miner.groovy   # Groovy miner lifecycle script
└── reports/                   # JMeter output (gitignored)
```

## Metrics

The load test measures:

Each protocol phase is recorded as a JMeter sub-result, so the aggregate
report and HTML dashboard contain one row per phase alongside the parent
`Stratum Miner Session` row:

| Metric | Target | Source (aggregate row) |
|--------|--------|------------------------|
| Subscribe latency (p95) | < 50ms | `stratum.subscribe` |
| Authorize latency (p95) | < 50ms | `stratum.authorize` |
| Time to first mining.notify | < 2s | `stratum.first_notify` |
| Submit throughput | baseline | `stratum.submit` (samples/s) |
| Submit latency (p95) | < 100ms | `stratum.submit` |
| Connection rate | > 100/s | Connection stress test |
| Error rate | < 1% | JMeter aggregate |

A `stratum.submit` sub-result is failed only when the server sends no
response — rejected shares (expected with random nonces) count as successful
samples, with the accepted/rejected split reported per session.

## How It Works

The stratum server dispatches mining jobs via the following pipeline:

```
bitcoind (regtest) ──IPC──> braidpool node ──TCP──> miners (JMeter)
     ↑                           │
  generate-blocks.sh      mining.notify broadcast
  (every 10s)                    │
                           mining.submit ──> share validation
```

- `generate-blocks.sh` creates blocks every 10s, triggering new templates via IPC
- The braidpool node receives templates and broadcasts `mining.notify` to all connected miners
- JMeter threads submit shares with random nonces and masked version bits (these fail PoW but exercise the full validation path, including BIP310 version-rolling)
- Share rejections are expected and counted — we're measuring processing throughput, not mining success. Each session's report breaks submits into accepted / rejected / no-response and records the first rejection reason, so protocol-level failures are distinguishable from expected PoW rejections
