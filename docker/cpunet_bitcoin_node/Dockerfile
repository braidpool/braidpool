FROM debian:bookworm-slim AS builder

RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    pkg-config \
    git \
    python3 \
    libssl-dev \
    libevent-dev \
    libboost-dev \
    libsqlite3-dev \
    capnproto \
    libcapnp-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build

RUN git clone \
    --branch cpunet \
    --depth 1 \
    https://github.com/braidpool/bitcoin.git \
    .

RUN cmake -B build \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_IPC=ON \
        -DBUILD_CLI=ON \
        -DBUILD_TESTS=OFF \
        -DBUILD_GUI=OFF \
        -DWITH_WALLET=OFF \
        -DWITH_BDB=OFF 

RUN cd build && make -j$(nproc)

FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y --no-install-recommends \
    libevent-2.1-7 \
    libevent-core-2.1-7 \
    libevent-extra-2.1-7 \
    libevent-pthreads-2.1-7 \
    libboost-filesystem1.81.0 \
    libboost-thread1.81.0 \
    libcapnp-0.9.2 \
    libsqlite3-0 \
    curl \
    && rm -rf /var/lib/apt/lists/*

RUN groupadd -r bitcoin && \
    useradd -r -g bitcoin -d /data -m bitcoin

COPY --from=builder /build/build/bin/bitcoin-node /usr/local/bin/bitcoin-node
COPY --from=builder /build/build/bin/bitcoin-cli  /usr/local/bin/bitcoin-cli

RUN mkdir -p /data/.bitcoin/cpunet /tmp/bitcoin-ipc && \
    chown -R bitcoin:bitcoin /data /tmp/bitcoin-ipc

COPY docker/cpunet_bitcoin_node/docker-entrypoint.sh /usr/local/bin/docker-entrypoint.sh
RUN chmod +x /usr/local/bin/docker-entrypoint.sh

USER bitcoin

ENV HOME=/data

VOLUME ["/data/.bitcoin", "/tmp/bitcoin-ipc"]

EXPOSE 28333
EXPOSE 28332
EXPOSE 38332
EXPOSE 38338

HEALTHCHECK --interval=15s --timeout=5s --start-period=60s --retries=5 \
    CMD bitcoin-cli \
        -cpunet \
        -datadir=/data/.bitcoin \
        -conf=/data/.bitcoin/bitcoin.conf \
        getblockcount || exit 1

ENTRYPOINT ["/usr/local/bin/docker-entrypoint.sh"]
CMD ["bitcoin-node", \
    "-cpunet", \
    "-datadir=/data/.bitcoin", \
    "-conf=/data/.bitcoin/bitcoin.conf", \
    "-debug=ipc", \
    "-printtoconsole"]