# Braidpool Miner API

Simplified REST API for monitoring Bitcoin miners with automatic polling.

## Quick Start

**Option 1: Run from braidpool directory**
```bash
cd braidpool
pip install -r miner_api/requirements.txt
uvicorn miner_api.main:app --host 0.0.0.0 --port 5001
```

**Option 2: Run from miner_api directory**
```bash
cd miner_api
pip install -r requirements.txt
uvicorn main:app --host 0.0.0.0 --port 5001
```
