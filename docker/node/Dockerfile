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

# Dummy main.rs to cache dependencies before copying the actual source code
RUN mkdir -p node/src braidpool-cli/src && \
echo "fn main() {}" > node/src/main.rs && \
echo "" > node/src/lib.rs && \
    echo "fn main() {}" > braidpool-cli/src/main.rs

RUN mkdir -p node/schema 
    
# Caching the dependency only build 
RUN cargo build --release --package node && \
    cargo build --release --package braidpool-cli

COPY node/src ./node/src/
COPY node/schema ./node/schema/
COPY node/build.rs ./node/build.rs
COPY braidpool-cli/src ./braidpool-cli/src/

RUN touch -a -m ./node/src/main.rs
RUN touch -a -m ./braidpool-cli/src/main.rs

RUN cargo build --release --package node && \
    cargo build --release --package braidpool-cli


# Runtime phase 
FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libsqlite3-0 \
    curl \
    dnsutils \
    && rm -rf /var/lib/apt/lists/*

# Creating non-root separate user 
RUN groupadd -r braidpool && useradd -r -g braidpool braidpool

RUN mkdir -p /app /data/.braidpool && \
    chown -R braidpool:braidpool /app /data

WORKDIR /app

COPY --from=builder /build/target/release/node /app/node
COPY --from=builder /build/target/release/braidpool-cli /app/braidpool-cli
COPY node/src/default_braidpool_config.toml /app/default_config.toml
COPY docker/node/docker-entrypoint.sh /app/docker-entrypoint.sh
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
    RUST_LOG=debug

EXPOSE 6680 6682 3333

VOLUME ["/data"]

HEALTHCHECK --interval=30s --timeout=10s --start-period=30s --retries=3 \
    CMD curl -sf http://localhost:6682/health || exit 1

ENTRYPOINT ["/app/docker-entrypoint.sh"]