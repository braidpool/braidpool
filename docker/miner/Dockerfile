FROM rust:1.88-slim AS builder

RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    git \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build

# Clone the rust_cpunet_miner repository
RUN git clone https://github.com/braidpool/rust_cpunet_miner.git .

# Build the miner in release mode
RUN cargo build --release

# Runtime phase
FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN groupadd -r miner && useradd -r -g miner miner

RUN mkdir -p /app && chown -R miner:miner /app

WORKDIR /app

COPY --from=builder /build/target/release/cpunet_miner /app/cpunet_miner
COPY docker/miner/docker-entrypoint.sh /app/docker-entrypoint.sh
RUN chmod +x /app/docker-entrypoint.sh /app/cpunet_miner && \
    chown -R miner:miner /app

USER miner

# Environment variables for miner configuration
ENV STRATUM_URL=stratum+tcp://braidpool-node:3333 \
    WORKER_USER=miner \
    WORKER_PASS=x \
    MINER_THREADS=1 \
    RUST_LOG=info \
    RETRY_DELAY=5

ENTRYPOINT ["/app/docker-entrypoint.sh"]