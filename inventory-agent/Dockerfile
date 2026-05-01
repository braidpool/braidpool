# syntax=docker/dockerfile:1

# ── build stage ──────────────────────────────────────────────────────────────
# Install deps into a separate layer so that rebuilds only re-run pip when
# requirements.txt actually changes.
FROM python:3.12-slim AS builder

WORKDIR /app

# Install only what we need for building, in one layer, without cache files
COPY requirements.txt .
RUN pip install --no-cache-dir --prefix=/install -r requirements.txt


# ── runtime stage ─────────────────────────────────────────────────────────────
FROM python:3.12-slim

# Create a non-root user so the process doesn't run as root inside the container
RUN addgroup --system inventory && adduser --system --ingroup inventory inventory

WORKDIR /app

# Pull in the installed packages from the builder stage
COPY --from=builder /install /usr/local

# Copy application source
COPY main.py models.py store.py ./

USER inventory

# Port the API listens on (can be overridden at runtime)
ENV PORT=8000

EXPOSE 8000

# Uvicorn with 1 worker is fine for an inventory service — scale horizontally
# via docker-compose replicas or Kubernetes if needed.
CMD ["uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8000"]
