# Braidpool Node Container Deployment

This document describes how to run containerized Braidpool nodes using Docker and Kubernetes.

## Quick Start

### Build the Docker Image

```bash
# From repository root
docker build -t braidpool/node:latest -f node/Dockerfile .
```

### Run a Single Node (Docker)

```bash
docker run -d \
  --name braidpool-node \
  -p 6680:6680 \
  -p 6682:6682 \
  -p 3333:3333 \
  -e BRAIDPOOL_NETWORK=cpunet \
  -e BRAIDPOOL_BITCOIN_HOST=host.docker.internal \
  -v braidpool-data:/data \
  braidpool/node:latest
```

### Running both the services under one 
```bash
docker compose -f /braidpool/docker-compose-combined.yaml up 

```