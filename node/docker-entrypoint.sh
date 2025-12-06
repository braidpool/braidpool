#!/bin/bash
# =============================================================================
# Braidpool Node Docker Entrypoint
# Configures the node from environment variables and starts it
# =============================================================================

set -e

# Print banner
echo "========================================"
echo "  Braidpool Node Container"
echo "========================================"
echo "Node ID: ${HOSTNAME}"
echo "Network: ${BRAIDPOOL_NETWORK:-cpunet}"
echo "Bind:    ${BRAIDPOOL_BIND:-0.0.0.0:6680}"
echo "========================================"

# Build command line arguments from environment variables
ARGS=""

# Data directory
if [ -n "${BRAIDPOOL_DATADIR}" ]; then
    ARGS="${ARGS} --datadir ${BRAIDPOOL_DATADIR}"
    # Ensure directory exists
    mkdir -p "${BRAIDPOOL_DATADIR}"
fi

# P2P bind address
if [ -n "${BRAIDPOOL_BIND}" ]; then
    ARGS="${ARGS} --bind ${BRAIDPOOL_BIND}"
fi

# Network selection
if [ -n "${BRAIDPOOL_NETWORK}" ]; then
    ARGS="${ARGS} --network ${BRAIDPOOL_NETWORK}"
fi

# Bitcoin connection
if [ -n "${BRAIDPOOL_BITCOIN_HOST}" ]; then
    ARGS="${ARGS} --bitcoin ${BRAIDPOOL_BITCOIN_HOST}"
fi

if [ -n "${BRAIDPOOL_BITCOIN_PORT}" ]; then
    ARGS="${ARGS} --rpcport ${BRAIDPOOL_BITCOIN_PORT}"
fi

# Bitcoin RPC authentication
if [ -n "${BRAIDPOOL_RPC_USER}" ]; then
    ARGS="${ARGS} --rpcuser ${BRAIDPOOL_RPC_USER}"
fi

if [ -n "${BRAIDPOOL_RPC_PASS}" ]; then
    ARGS="${ARGS} --rpcpass ${BRAIDPOOL_RPC_PASS}"
fi

if [ -n "${BRAIDPOOL_RPC_COOKIE}" ]; then
    ARGS="${ARGS} --rpccookie ${BRAIDPOOL_RPC_COOKIE}"
fi

# IPC socket
if [ -n "${BRAIDPOOL_IPC_SOCKET}" ]; then
    ARGS="${ARGS} --ipc-socket ${BRAIDPOOL_IPC_SOCKET}"
fi

# Peer nodes (comma-separated list)
if [ -n "${BRAIDPOOL_PEERS}" ]; then
    IFS=',' read -ra PEER_ARRAY <<< "${BRAIDPOOL_PEERS}"
    for peer in "${PEER_ARRAY[@]}"; do
        # Trim whitespace
        peer=$(echo "$peer" | xargs)
        if [ -n "$peer" ]; then
            ARGS="${ARGS} --addnode ${peer}"
        fi
    done
fi

# Additional custom arguments passed to container
if [ -n "${BRAIDPOOL_EXTRA_ARGS}" ]; then
    ARGS="${ARGS} ${BRAIDPOOL_EXTRA_ARGS}"
fi

echo "Starting node with arguments: ${ARGS}"
echo "========================================"

# Execute the node binary with constructed arguments
# If additional arguments are passed to the container, append them
exec /app/node ${ARGS} "$@"
