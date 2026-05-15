#!/bin/bash

set -e
ARGS=""

# Resolve *_FILE env vars (docker secrets convention) into their plain counterparts.
for var in BRAIDPOOL_RPC_USER BRAIDPOOL_RPC_PASS BRAIDPOOL_RPC_COOKIE; do
    file_var="${var}_FILE"
    if [ -n "${!file_var}" ] && [ -r "${!file_var}" ]; then
        export "${var}"="$(cat "${!file_var}")"
    fi
done

if [ -n "${BRAIDPOOL_DATADIR}" ]; then
    ARGS="${ARGS} --datadir ${BRAIDPOOL_DATADIR}"
    mkdir -p "${BRAIDPOOL_DATADIR}"
fi

if [ -n "${BRAIDPOOL_BIND}" ]; then
    ARGS="${ARGS} --bind ${BRAIDPOOL_BIND}"
fi

if [ -n "${BRAIDPOOL_NETWORK}" ]; then
    ARGS="${ARGS} --network ${BRAIDPOOL_NETWORK}"
fi

if [ -n "${BRAIDPOOL_BITCOIN_HOST}" ]; then
    ARGS="${ARGS} --bitcoin ${BRAIDPOOL_BITCOIN_HOST}"
fi

if [ -n "${BRAIDPOOL_BITCOIN_PORT}" ]; then
    ARGS="${ARGS} --rpcport ${BRAIDPOOL_BITCOIN_PORT}"
fi

if [ -n "${BRAIDPOOL_RPC_USER}" ]; then
    ARGS="${ARGS} --rpcuser ${BRAIDPOOL_RPC_USER}"
fi

if [ -n "${BRAIDPOOL_RPC_PASS}" ]; then
    ARGS="${ARGS} --rpcpass ${BRAIDPOOL_RPC_PASS}"
fi

if [ -n "${BRAIDPOOL_RPC_COOKIE}" ]; then
    ARGS="${ARGS} --rpccookie ${BRAIDPOOL_RPC_COOKIE}"
fi

if [ -n "${BRAIDPOOL_IPC_SOCKET}" ]; then
    ARGS="${ARGS} --ipc-socket ${BRAIDPOOL_IPC_SOCKET}"
fi

if [ -n "${BRAIDPOOL_PEERS}" ]; then
    IFS=',' read -ra PEER_ARRAY <<< "${BRAIDPOOL_PEERS}"
    for peer in "${PEER_ARRAY[@]}"; do
        peer=$(echo "$peer" | xargs)
        if [ -n "$peer" ]; then
            ARGS="${ARGS} --addnode ${peer}"
        fi
    done
fi

if [ -n "${BRAIDPOOL_EXTRA_ARGS}" ]; then
    ARGS="${ARGS} ${BRAIDPOOL_EXTRA_ARGS}"
fi

echo "Starting node with arguments: ${ARGS}"

exec /app/node ${ARGS} "$@"