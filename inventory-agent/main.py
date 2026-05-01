"""
Braidpool Inventory Agent

A FastAPI-based service that manages and reports on the inventory of mining
devices connected to a Braidpool node. Supports ASIC miners (e.g. Antminer,
Whatsminer) and CPU miners used in cpunet/testing environments.
"""

import logging
from contextlib import asynccontextmanager
from typing import Optional

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware

from models import (
    Miner,
    MinerCreate,
    MinerUpdate,
    MinerType,
    MinerStatus,
    InventorySummary,
)
from store import MinerStore

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

store = MinerStore()


@asynccontextmanager
async def lifespan(app: FastAPI):
    logger.info("Inventory Agent starting up")
    store.seed_defaults()
    yield
    logger.info("Inventory Agent shutting down")


app = FastAPI(
    title="Braidpool Inventory Agent",
    description=(
        "Tracks and manages ASIC and CPU miners connected to a Braidpool node. "
        "Provides status, hashrate, temperature, and alert information per device."
    ),
    version="0.1.0",
    lifespan=lifespan,
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"], 
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.get("/health", tags=["meta"])
def health():
    return {"status": "ok"}



@app.get("/miners", response_model=list[Miner], tags=["miners"])
def list_miners(
    status: Optional[MinerStatus] = None,
    miner_type: Optional[MinerType] = None,
):
    """Return all miners, optionally filtered by status or type."""
    miners = store.all()
    if status is not None:
        miners = [m for m in miners if m.status == status]
    if miner_type is not None:
        miners = [m for m in miners if m.miner_type == miner_type]
    return miners


@app.get("/miners/summary", response_model=InventorySummary, tags=["miners"])
def inventory_summary():
    """Aggregate counts and totals across all miners."""
    miners = store.all()
    online = [m for m in miners if m.status == MinerStatus.online]
    warning = [m for m in miners if m.status == MinerStatus.warning]
    offline = [m for m in miners if m.status == MinerStatus.offline]

    total_hashrate = sum(
        float(m.hashrate_th) for m in online + warning if m.hashrate_th is not None
    )
    total_power = sum(
        int(m.power_draw_w) for m in online + warning if m.power_draw_w is not None
    )

    return InventorySummary(
        total=len(miners),
        online=len(online),
        warning=len(warning),
        offline=len(offline),
        total_hashrate_th=round(total_hashrate, 2),
        total_power_w=total_power,
    )


@app.get("/miners/{miner_id}", response_model=Miner, tags=["miners"])
def get_miner(miner_id: str):
    """Return a single miner by ID."""
    miner = store.get(miner_id)
    if miner is None:
        raise HTTPException(status_code=404, detail=f"Miner '{miner_id}' not found")
    return miner


@app.post("/miners", response_model=Miner, status_code=201, tags=["miners"])
def create_miner(body: MinerCreate):
    """Register a new miner in the inventory."""
    miner = store.create(body)
    logger.info("Registered miner %s (%s)", miner.id, miner.name)
    return miner


@app.patch("/miners/{miner_id}", response_model=Miner, tags=["miners"])
def update_miner(miner_id: str, body: MinerUpdate):
    """Update mutable fields on an existing miner (status, hashrate, temp, etc.)."""
    miner = store.update(miner_id, body)
    if miner is None:
        raise HTTPException(status_code=404, detail=f"Miner '{miner_id}' not found")
    return miner


@app.delete("/miners/{miner_id}", status_code=204, tags=["miners"])
def delete_miner(miner_id: str):
    """Remove a miner from the inventory."""
    removed = store.delete(miner_id)
    if not removed:
        raise HTTPException(status_code=404, detail=f"Miner '{miner_id}' not found")
