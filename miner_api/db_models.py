from sqlalchemy import Column, Integer, String, Float, Boolean, DateTime, JSON, Text
from sqlalchemy.sql import func
from datetime import datetime, timezone
import uuid

from .database import Base


class MinerDevice(Base):    
    __tablename__ = "miner_devices"
    
    id = Column(String(36), primary_key=True, default=lambda: str(uuid.uuid4()))
    ip = Column(String(45), unique=True, nullable=False, index=True)  # IPv4 or IPv6
    name = Column(String(255), nullable=True)  # User-defined name for the miner
    
    # Device identification
    hostname = Column(String(255), nullable=True)
    mac = Column(String(17), nullable=True)
    make = Column(String(100), nullable=True)
    model = Column(String(100), nullable=True)
    firmware = Column(String(100), nullable=True)
    
    # Performance metrics
    hashrate_current = Column(Float, nullable=True)
    hashrate_avg = Column(Float, nullable=True)
    expected_hashrate = Column(Float, nullable=True)
    
    # Temperature readings
    temperature = Column(Float, nullable=True)
    temperature_max = Column(Float, nullable=True)
    vr_temperature = Column(Float, nullable=True)
    
    # Power metrics
    power_usage = Column(Integer, nullable=True)
    power_limit = Column(Integer, nullable=True)
    efficiency = Column(Float, nullable=True)
    voltage = Column(Float, nullable=True)
    
    # Hardware status
    fan_speeds = Column(JSON, default=list)  
    chip_count = Column(Integer, nullable=True)
    is_mining = Column(Boolean, nullable=True)
    errors = Column(JSON, default=list) 
    uptime = Column(Integer, nullable=True)
    
    # Pool information
    pools = Column(JSON, default=list)  
    primary_pool = Column(String(255), default="No Pool")
    
    # API info
    api_version = Column(String(50), nullable=True)
    
    # Connection status
    is_online = Column(Boolean, default=True)
    last_error = Column(Text, nullable=True)
    
    # Timestamps
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    updated_at = Column(DateTime(timezone=True), server_default=func.now(), onupdate=func.now())
    last_seen = Column(DateTime(timezone=True), nullable=True)  
    
    def __repr__(self):
        return f"<MinerDevice(ip={self.ip}, model={self.model}, is_online={self.is_online})>"
    
    def to_dict(self):
        """Convert model to dictionary for API responses."""
        return {
            "id": self.id,
            "ip": self.ip,
            "name": self.name,
            "hostname": self.hostname,
            "mac": self.mac,
            "make": self.make,
            "model": self.model,
            "firmware": self.firmware,
            "hashrate_current": self.hashrate_current,
            "hashrate_avg": self.hashrate_avg,
            "expected_hashrate": self.expected_hashrate,
            "temperature": self.temperature,
            "temperature_max": self.temperature_max,
            "vr_temperature": self.vr_temperature,
            "power_usage": self.power_usage,
            "power_limit": self.power_limit,
            "efficiency": self.efficiency,
            "voltage": self.voltage,
            "fan_speeds": self.fan_speeds or [],
            "chip_count": self.chip_count,
            "is_mining": self.is_mining,
            "errors": self.errors or [],
            "uptime": self.uptime,
            "pools": self.pools or [],
            "primary_pool": self.primary_pool,
            "api_version": self.api_version,
            "is_online": self.is_online,
            "last_error": self.last_error,
            "created_at": self.created_at.isoformat() if self.created_at else None,
            "updated_at": self.updated_at.isoformat() if self.updated_at else None,
            "last_seen": self.last_seen.isoformat() if self.last_seen else None,
        }

    @classmethod
    def from_miner_data(cls, ip: str, data: dict, name: str = None, existing_id: str = None):
        """Create or update a MinerDevice from normalized miner data."""
        pools_data = []
        for pool in data.get("pools", []):
            if isinstance(pool, dict):
                pools_data.append(pool)
            else:
                pools_data.append(pool.model_dump() if hasattr(pool, 'model_dump') else dict(pool))
        
        kwargs = {
            "ip": ip,
            "name": name,
            "hostname": data.get("hostname"),
            "mac": data.get("mac"),
            "make": data.get("make"),
            "model": data.get("model"),
            "firmware": data.get("firmware"),
            "hashrate_current": data.get("hashrate_current"),
            "hashrate_avg": data.get("hashrate_avg"),
            "expected_hashrate": data.get("expected_hashrate"),
            "temperature": data.get("temperature"),
            "temperature_max": data.get("temperature_max"),
            "vr_temperature": data.get("vr_temperature"),
            "power_usage": data.get("power_usage"),
            "power_limit": data.get("power_limit"),
            "efficiency": data.get("efficiency"),
            "voltage": data.get("voltage"),
            "fan_speeds": data.get("fan_speeds", []),
            "chip_count": data.get("chip_count"),
            "is_mining": data.get("is_mining"),
            "errors": data.get("errors", []),
            "uptime": data.get("uptime"),
            "pools": pools_data,
            "primary_pool": data.get("primary_pool", "No Pool"),
            "api_version": data.get("api_version"),
            "is_online": True,
            "last_error": None,
            "last_seen": datetime.now(timezone.utc),
        }
        
        if existing_id:
            kwargs["id"] = existing_id
        
        return cls(**kwargs)
