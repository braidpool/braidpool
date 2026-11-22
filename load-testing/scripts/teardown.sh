#!/usr/bin/env bash
# Stop all load test infrastructure
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOAD_TEST_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
PIDFILE_DIR="${LOAD_TEST_DIR}/.pids"

BITCOIN_DATADIR="${BITCOIN_DATADIR:-/tmp/braidpool-loadtest-bitcoin}"
RPC_USER="${RPC_USER:-loadtest}"
RPC_PASS="${RPC_PASS:-loadtest}"
RPC_PORT="${BITCOIN_RPC_PORT:-18443}"

BITCOIN_CLI_BIN="${BITCOIN_CLI_BIN:-$(command -v bitcoin-cli || true)}"

echo "=== Braidpool Load Test Teardown ==="

if [ -f "$PIDFILE_DIR/generate-blocks.pid" ]; then
    GEN_PID=$(cat "$PIDFILE_DIR/generate-blocks.pid")
    if kill -0 "$GEN_PID" 2>/dev/null; then
        echo "Stopping block generator (PID: $GEN_PID)..."
        kill -9 "$GEN_PID" 2>/dev/null || true
        wait "$GEN_PID" 2>/dev/null || true
    fi
    rm -f "$PIDFILE_DIR/generate-blocks.pid"
fi

if [ -f "$PIDFILE_DIR/braidpool.pid" ]; then
    BP_PID=$(cat "$PIDFILE_DIR/braidpool.pid")
    if kill -0 "$BP_PID" 2>/dev/null; then
        echo "Stopping braidpool-node (PID: $BP_PID)..."
        kill "$BP_PID" 2>/dev/null || true
        # Give it a moment to shut down gracefully
        sleep 2
        kill -9 "$BP_PID" 2>/dev/null || true
    fi
    rm -f "$PIDFILE_DIR/braidpool.pid"
fi

echo "Stopping bitcoin-node..."
if [ -n "$BITCOIN_CLI_BIN" ]; then
    "$BITCOIN_CLI_BIN" -regtest -datadir="$BITCOIN_DATADIR" -rpcuser="$RPC_USER" -rpcpassword="$RPC_PASS" -rpcport="$RPC_PORT" \
        stop 2>/dev/null || true
else
    echo "  bitcoin-cli not found (set BITCOIN_CLI_BIN); skipping graceful stop"
fi

# Wait for bitcoin-node to stop
MAX_WAIT=15
WAITED=0
while pgrep -f "bitcoin-node.*$BITCOIN_DATADIR" > /dev/null 2>&1; do
    sleep 1
    WAITED=$((WAITED + 1))
    if [ "$WAITED" -ge "$MAX_WAIT" ]; then
        echo "  WARNING: bitcoin-node did not stop gracefully, force killing..."
        pkill -9 -f "bitcoin-node.*$BITCOIN_DATADIR" 2>/dev/null || true
        break
    fi
done

rm -f "$PIDFILE_DIR/mining-address.txt"
rm -f /tmp/bitcoin-loadtest-regtest.sock

echo ""
echo "=== Teardown Complete ==="
echo "Bitcoin datadir preserved at: $BITCOIN_DATADIR"
echo "To remove: rm -rf $BITCOIN_DATADIR"
