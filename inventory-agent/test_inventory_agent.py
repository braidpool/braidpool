"""
Tests for the Inventory Agent REST API.

Run with:
    cd inventory-agent
    pip install -r requirements.txt pytest httpx
    pytest test_inventory_agent.py -v
"""

import pytest
from fastapi.testclient import TestClient

from main import app, store
from models import MinerStatus, MinerType


@pytest.fixture(autouse=True)
def reset_store():
    """Reset the store before every test so tests don't bleed into each other."""
    store._miners.clear()
    store.seed_defaults()
    yield
    store._miners.clear()


client = TestClient(app)


# ---------------------------------------------------------------------------
# Health
# ---------------------------------------------------------------------------

def test_health():
    response = client.get("/health")
    assert response.status_code == 200
    assert response.json() == {"status": "ok"}


# ---------------------------------------------------------------------------
# GET /miners
# ---------------------------------------------------------------------------

def test_list_miners_returns_all_seeded():
    response = client.get("/miners")
    assert response.status_code == 200
    miners = response.json()
    # Seed data has 8 ASIC + 1 CPU
    assert len(miners) == 9


def test_list_miners_filter_by_status_online():
    response = client.get("/miners?status=online")
    assert response.status_code == 200
    miners = response.json()
    assert all(m["status"] == "online" for m in miners)
    assert len(miners) > 0


def test_list_miners_filter_by_status_offline():
    response = client.get("/miners?status=offline")
    assert response.status_code == 200
    miners = response.json()
    assert all(m["status"] == "offline" for m in miners)


def test_list_miners_filter_by_type_cpu():
    response = client.get("/miners?miner_type=cpu")
    assert response.status_code == 200
    miners = response.json()
    assert all(m["miner_type"] == "cpu" for m in miners)
    assert len(miners) == 1


def test_list_miners_filter_by_type_asic():
    response = client.get("/miners?miner_type=asic")
    assert response.status_code == 200
    miners = response.json()
    assert all(m["miner_type"] == "asic" for m in miners)
    assert len(miners) == 8


# ---------------------------------------------------------------------------
# GET /miners/summary
# ---------------------------------------------------------------------------

def test_summary_totals_add_up():
    response = client.get("/miners/summary")
    assert response.status_code == 200
    s = response.json()
    assert s["online"] + s["warning"] + s["offline"] == s["total"]


def test_summary_total_hashrate_is_positive():
    response = client.get("/miners/summary")
    assert response.status_code == 200
    assert response.json()["total_hashrate_th"] > 0


# ---------------------------------------------------------------------------
# GET /miners/{id}
# ---------------------------------------------------------------------------

def test_get_existing_miner():
    response = client.get("/miners/miner-001")
    assert response.status_code == 200
    data = response.json()
    assert data["id"] == "miner-001"
    assert data["miner_type"] == "asic"


def test_get_nonexistent_miner_returns_404():
    response = client.get("/miners/miner-does-not-exist")
    assert response.status_code == 404


# ---------------------------------------------------------------------------
# POST /miners
# ---------------------------------------------------------------------------

def test_create_asic_miner():
    payload = {
        "name": "Antminer S21",
        "miner_type": "asic",
        "location": "Rack D, Unit 1",
        "status": "online",
        "hashrate_th": 200.0,
        "temp_c": 60.0,
        "efficiency_j_th": 17.5,
        "power_draw_w": 3500,
        "uptime_pct": 100.0,
        "last_seen": "just now",
        "alerts": 0,
    }
    response = client.post("/miners", json=payload)
    assert response.status_code == 201
    data = response.json()
    assert data["name"] == "Antminer S21"
    assert data["miner_type"] == "asic"
    assert data["hashrate_th"] == 200.0
    assert "id" in data


def test_create_cpu_miner():
    payload = {
        "name": "cpunet-node-1",
        "miner_type": "cpu",
        "status": "online",
        "alerts": 0,
    }
    response = client.post("/miners", json=payload)
    assert response.status_code == 201
    assert response.json()["miner_type"] == "cpu"


def test_create_miner_missing_required_field_returns_422():
    # `name` is required
    response = client.post("/miners", json={"miner_type": "asic"})
    assert response.status_code == 422


# ---------------------------------------------------------------------------
# PATCH /miners/{id}
# ---------------------------------------------------------------------------

def test_update_miner_status():
    response = client.patch("/miners/miner-001", json={"status": "warning", "alerts": 1})
    assert response.status_code == 200
    data = response.json()
    assert data["status"] == "warning"
    assert data["alerts"] == 1
    # Fields not in the patch body should be unchanged
    assert data["name"] == "Antminer S19"


def test_update_miner_hashrate():
    response = client.patch("/miners/miner-001", json={"hashrate_th": 100.0})
    assert response.status_code == 200
    assert response.json()["hashrate_th"] == 100.0


def test_update_nonexistent_miner_returns_404():
    response = client.patch("/miners/no-such-miner", json={"status": "offline"})
    assert response.status_code == 404


# ---------------------------------------------------------------------------
# DELETE /miners/{id}
# ---------------------------------------------------------------------------

def test_delete_miner():
    response = client.delete("/miners/miner-001")
    assert response.status_code == 204
    # Confirm it's actually gone
    assert client.get("/miners/miner-001").status_code == 404


def test_delete_nonexistent_miner_returns_404():
    response = client.delete("/miners/ghost-miner")
    assert response.status_code == 404
