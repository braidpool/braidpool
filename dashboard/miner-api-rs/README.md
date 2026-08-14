Run the HTTP API server (port 5001, auto-scans LAN every 5 min):

```bash
cargo run -p miner-api-rs --bin server
```

### Debugging field mismatches

If the values shown in the UI don't match your miner's own web dashboard, call the
debug endpoint. It re-probes the miner live and returns **every raw field from
asic-rs** alongside the normalized values that the UI actually displays:

```bash
# replace <id> with the miner's UUID from GET /api/miners
curl http://localhost:5001/api/miners/<id>/debug | jq .
```
