#!/bin/bash
set -e

# Reading secrets from the files and passing them to the config file
read_secret() {
    local var_name="$1"
    local file_var="${var_name}_FILE"
    local file_path="${!file_var}"

    if [ -n "${file_path}" ] && [ -r "${file_path}" ]; then
        cat "${file_path}"
    else
        echo "${!var_name}"
    fi
}

RPC_USER="$(read_secret BITCOIN_RPC_USER)"
RPC_PASSWORD="$(read_secret BITCOIN_RPC_PASSWORD)"

if [ -z "${RPC_USER}" ] || [ -z "${RPC_PASSWORD}" ]; then
    echo "ERROR: BITCOIN_RPC_USER and BITCOIN_RPC_PASSWORD must be set (or *_FILE pointing to a readable secret)." >&2
    exit 1
fi

CONF_FILE="/data/.bitcoin/bitcoin.conf"
mkdir -p "$(dirname "${CONF_FILE}")"

# Writing to the config file at the given path
cat > "${CONF_FILE}" <<EOF
[cpunet]
server=1
rpcuser=${RPC_USER}
rpcpassword=${RPC_PASSWORD}
rpcbind=0.0.0.0
rpcallowip=0.0.0.0/0
zmqpubsequence=tcp://0.0.0.0:38338
zmqpubhashblock=tcp://0.0.0.0:38332
ipcbind=unix:/tmp/bitcoin-ipc/bitcoin.sock
debug=ipc
printtoconsole=1
EOF

exec "$@"
