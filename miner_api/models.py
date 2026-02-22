"""Pydantic models for request/response validation."""

from pydantic import BaseModel, Field
from typing import List, Optional
from datetime import datetime


class PoolInfo(BaseModel):
    """Pool configuration information."""
    url: Optional[str] = None
    user: Optional[str] = None
    status: Optional[str] = None


class MinerData(BaseModel):
    """Normalized miner data response."""
    ip: Optional[str] = None
    hostname: Optional[str] = None
    mac: Optional[str] = None
    make: Optional[str] = None
    model: Optional[str] = None
    firmware: Optional[str] = None
    hashrate_current: Optional[float] = None
    hashrate_avg: Optional[float] = None
    expected_hashrate: Optional[float] = None
    temperature: Optional[float] = None
    temperature_max: Optional[float] = None
    vr_temperature: Optional[float] = None
    power_usage: Optional[int] = None
    power_limit: Optional[int] = None
    efficiency: Optional[float] = None
    voltage: Optional[float] = None
    fan_speeds: List[int] = Field(default_factory=list)
    chip_count: Optional[int] = None
    is_mining: Optional[bool] = None
    errors: List[str] = Field(default_factory=list)
    uptime: Optional[int] = None
    pools: List[PoolInfo] = Field(default_factory=list)
    primary_pool: str = "No Pool"
    api_version: Optional[str] = None
    timestamp: Optional[datetime] = None
