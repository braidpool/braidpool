#!/usr/bin/env bash
# Periodically generate blocks in regtest to keep new templates flowing
# This triggers TipChanged → IPC → new mining.notify to all connected miners
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOAD_TEST_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
PIDFILE_DIR="${LOAD_TEST_DIR}/.pids"

# Configuration
BITCOIN_DATADIR="${BITCOIN_DATADIR:-/tmp/braidpool-loadtest-bitcoin}"
RPC_USER="${RPC_USER:-loadtest}"
RPC_PASS="${RPC_PASS:-loadtest}"
RPC_PORT="${BITCOIN_RPC_PORT:-18443}"
BLOCK_INTERVAL="${BLOCK_INTERVAL:-10}"  # seconds between blocks

# Override via BITCOIN_CLI_BIN when bitcoin-cli is not in PATH
BITCOIN_CLI_BIN="${BITCOIN_CLI_BIN:-$(command -v bitcoin-cli || true)}"
if [ -z "$BITCOIN_CLI_BIN" ] || ! command -v "$BITCOIN_CLI_BIN" &>/dev/null; then
    echo "ERROR: bitcoin-cli binary not found. Set BITCOIN_CLI_BIN, e.g.:"
    echo "  export BITCOIN_CLI_BIN=\$HOME/bitcoin/build/bin/bitcoin-cli"
    exit 1
fi

MINING_ADDRESS_FILE="$PIDFILE_DIR/mining-address.txt"
if [ ! -f "$MINING_ADDRESS_FILE" ]; then
    echo "ERROR: Mining address file not found. Run setup-regtest.sh first."
    exit 1
fi

MINING_ADDRESS=$(cat "$MINING_ADDRESS_FILE")
BLOCK_NUM=0

echo "Block generator started (interval: ${BLOCK_INTERVAL}s, address: ${MINING_ADDRESS:0:20}...)"

cleanup() {
    echo "Block generator stopping (generated $BLOCK_NUM blocks)"
    exit 0
}
trap cleanup SIGTERM SIGINT

while true; do
    sleep "$BLOCK_INTERVAL"

    if "$BITCOIN_CLI_BIN" -regtest -datadir="$BITCOIN_DATADIR" -rpcuser="$RPC_USER" -rpcpassword="$RPC_PASS" -rpcport="$RPC_PORT" \
        generatetoaddress 1 "$MINING_ADDRESS" > /dev/null 2>&1; then
        BLOCK_NUM=$((BLOCK_NUM + 1))
        HEIGHT=$("$BITCOIN_CLI_BIN" -regtest -datadir="$BITCOIN_DATADIR" -rpcuser="$RPC_USER" -rpcpassword="$RPC_PASS" -rpcport="$RPC_PORT" \
            getblockcount 2>/dev/null || echo "?")
        echo "  Block #${BLOCK_NUM} generated (height: $HEIGHT)"
    else
        echo "  WARNING: Failed to generate block (bitcoind may be stopping)"
    fi
done
