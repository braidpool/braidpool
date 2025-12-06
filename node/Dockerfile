FROM rust:1.88-slim AS builder

RUN apt-get update && apt-get install -y \
    capnproto \
    libcapnp-dev \
    libsqlite3-dev \
    pkg-config \
    cmake \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build

COPY Cargo.toml Cargo.lock ./
COPY node/Cargo.toml ./node/
COPY braidpool-cli/Cargo.toml ./braidpool-cli/

RUN mkdir -p node/src braidpool-cli/src && \
    echo "fn main() {}" > node/src/main.rs && \
    echo "" > node/src/lib.rs && \
    echo "fn main() {}" > braidpool-cli/src/main.rs

RUN mkdir -p node/schema && \
    printf '@0xdbb9ad1f14bf0b36;\n' > node/schema/placeholder.capnp

RUN cargo build --release --package node

COPY node/src ./node/src/
COPY node/schema ./node/schema/
COPY node/build.rs ./node/build.rs
COPY braidpool-cli/src ./braidpool-cli/src/

RUN find /build/target/release/.fingerprint -name "node-*" -exec rm -rf {} + 2>/dev/null || true && \
    find /build/target/release/.fingerprint -name "braidpool-cli-*" -exec rm -rf {} + 2>/dev/null || true

RUN cargo build --release --package node

RUN ls -la /build/target/release/node


FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libsqlite3-0 \
    curl \
    dnsutils \
    && rm -rf /var/lib/apt/lists/*

RUN groupadd -r braidpool && useradd -r -g braidpool braidpool

RUN mkdir -p /app /data/.braidpool && \
    chown -R braidpool:braidpool /app /data

WORKDIR /app

COPY --from=builder /build/target/release/node /app/node
COPY node/src/default_braidpool_config.toml /app/default_config.toml
COPY node/docker-entrypoint.sh /app/docker-entrypoint.sh
RUN chmod +x /app/docker-entrypoint.sh && chown -R braidpool:braidpool /app

USER braidpool

ENV HOME=/data \
    BRAIDPOOL_DATADIR=/data/.braidpool \
    BRAIDPOOL_BIND=0.0.0.0:6680 \
    BRAIDPOOL_NETWORK=cpunet \
    BRAIDPOOL_BITCOIN_HOST=host.docker.internal \
    BRAIDPOOL_BITCOIN_PORT=8332 \
    BRAIDPOOL_IPC_SOCKET=/data/.braidpool/bitcoin.sock \
    BRAIDPOOL_PEERS="" \
    RUST_LOG=info

EXPOSE 6680 6682 3333

VOLUME ["/data"]

HEALTHCHECK --interval=30s --timeout=10s --start-period=30s --retries=3 \
    CMD curl -sf http://localhost:6682/health || exit 1

ENTRYPOINT ["/app/docker-entrypoint.sh"]