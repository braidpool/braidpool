#!/bin/bash

# Retry settings
RETRY_DELAY=${RETRY_DELAY:-5}  

# Build command arguments
ARGS="-o ${STRATUM_URL} -O ${WORKER_USER}:${WORKER_PASS} -t ${MINER_THREADS} --debug"

# Run miner in a loop, restarting on failure until connected
while true; do
    echo "Starting cpunet_miner with: ${ARGS}"
    /app/cpunet_miner ${ARGS}
    EXIT_CODE=$?
    echo "Miner exited with code ${EXIT_CODE}, retrying in ${RETRY_DELAY}s..."
    sleep "${RETRY_DELAY}"
done