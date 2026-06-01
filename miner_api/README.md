# Braidpool Miner API

Simplified REST API for monitoring Bitcoin miners with persistent storage and automatic data refresh.

## Quick Start
```bash
pip install -r miner_api/requirements.txt
uvicorn miner_api.main:app --host 0.0.0.0 --port 5001
```

## API Endpoints

### Health
- `GET /api/health` - Health check

### Live Miner Query (No Storage)
- `GET /api/miners/live?ip=xxx.xxx.x.xxx` - Query miner directly without storing

### Stored Miners (Database-backed)
- `POST /api/miners` - Add a miner device to database
  ```json
  {"ip": "192.168.1.100", "name": "Miner 1"}
  ```
- `GET /api/miners` - Get all stored miners with cached data
- `GET /api/miners/{id}` - Get a specific miner by ID
- `PUT /api/miners/{id}` - Update miner details (name)
  ```json
  {"name": "New Name"}
  ```
- `DELETE /api/miners/{id}` - Remove miner from database
- `POST /api/miners/{id}/refresh` - Manually refresh a single miner's data
- `POST /api/miners/refresh/all` - Manually refresh all miners' data



## Interactive Docs

- Swagger UI: http://localhost:5001/docs
- ReDoc: http://localhost:5001/redoc
