"""
Pydantic models for the Braidpool Inventory Agent.

Two miner types are supported:
  - asic  : hardware miners (Antminer, Whatsminer, etc.)
  - cpu   : software miners used in cpunet / local testing
"""

from enum import Enum
from typing import Optional
from pydantic import BaseModel, Field


class MinerType(str, Enum):
    asic = "asic"
    cpu = "cpu"


class MinerStatus(str, Enum):
    online = "online"
    warning = "warning"
    offline = "offline"


class MinerBase(BaseModel):
    name: str = Field(..., examples=["Antminer S19 Pro"])
    miner_type: MinerType = Field(..., examples=[MinerType.asic])
    location: Optional[str] = Field(None, examples=["Rack A, Unit 3"])

    # Live metrics — None when the miner is offline
    status: MinerStatus = Field(MinerStatus.offline)
    hashrate_th: Optional[float] = Field(None, description="Hashrate in TH/s", examples=[95.2])
    temp_c: Optional[float] = Field(None, description="Board temperature in °C", examples=[65.0])
    efficiency_j_th: Optional[float] = Field(None, description="Efficiency in J/TH", examples=[34.5])
    power_draw_w: Optional[int] = Field(None, description="Power draw in watts", examples=[3250])
    uptime_pct: Optional[float] = Field(None, description="Uptime percentage 0–100", examples=[99.7])
    last_seen: Optional[str] = Field(None, examples=["2 mins ago"])
    alerts: int = Field(0, description="Number of active alerts")


class MinerCreate(MinerBase):
    """Fields accepted when registering a new miner."""
    pass


class MinerUpdate(BaseModel):
    """All fields are optional — only supplied fields are updated."""
    name: Optional[str] = None
    location: Optional[str] = None
    status: Optional[MinerStatus] = None
    hashrate_th: Optional[float] = None
    temp_c: Optional[float] = None
    efficiency_j_th: Optional[float] = None
    power_draw_w: Optional[int] = None
    uptime_pct: Optional[float] = None
    last_seen: Optional[str] = None
    alerts: Optional[int] = None


class Miner(MinerBase):
    """Full miner representation returned by the API."""
    id: str = Field(..., examples=["miner-001"])

    model_config = {"from_attributes": True}


class InventorySummary(BaseModel):
    """Aggregate statistics across all registered miners."""
    total: int
    online: int
    warning: int
    offline: int
    total_hashrate_th: float = Field(description="Sum of hashrates for online+warning miners")
    total_power_w: int = Field(description="Sum of power draw for online+warning miners")
