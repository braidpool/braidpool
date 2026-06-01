
import asyncio
from typing import Optional, List
from sqlalchemy import select
from sqlalchemy.ext.asyncio import AsyncSession
from datetime import datetime, timezone
import logging

from .db_models import MinerDevice
from .services import MinerService

logger = logging.getLogger("miner_api")


class MinerDBService:
    
    @staticmethod
    async def add_miner(db: AsyncSession, ip: str, name: Optional[str] = None) -> dict:
        """Add a new miner device to the database and fetch its initial data."""
        existing = await MinerDBService.get_miner_by_ip(db, ip) # Check if miner already exists
        if existing:
            return {
                "success": False,
                "error": f"Miner with IP {ip} already exists",
                "miner": existing.to_dict()
            }
        
        result = await MinerService.get_miner_data(ip)
        
        if not result.get("success"):
            miner = MinerDevice(
                ip=ip,
                name=name,
                is_online=False,
                last_error=result.get("error", "Failed to connect"),
            )
            db.add(miner)
            await db.commit()  
            await db.refresh(miner)
            
            return {
                "success": True,
                "warning": "Miner added but currently offline",
                "miner": miner.to_dict()
            }
        
        miner = MinerDevice.from_miner_data(ip, result["data"], name=name)
        db.add(miner)
        await db.commit()  
        await db.refresh(miner)
        
        logger.info(f"Added new miner device: {ip} (model: {miner.model})")
        
        return {
            "success": True,
            "miner": miner.to_dict()
        }
    
    @staticmethod
    async def get_miner_by_ip(db: AsyncSession, ip: str) -> Optional[MinerDevice]:
        """Get a miner by IP address."""
        result = await db.execute(
            select(MinerDevice).where(MinerDevice.ip == ip)
        )
        return result.scalar_one_or_none()
    
    @staticmethod
    async def get_miner_by_id(db: AsyncSession, miner_id: str) -> Optional[MinerDevice]:
        """Get a miner by ID."""
        result = await db.execute(
            select(MinerDevice).where(MinerDevice.id == miner_id)
        )
        return result.scalar_one_or_none()
    
    @staticmethod
    async def get_all_miners(db: AsyncSession) -> List[MinerDevice]:
        """Get all stored miners."""
        result = await db.execute(
            select(MinerDevice).order_by(MinerDevice.created_at.desc())
        )
        return list(result.scalars().all())
    
    @staticmethod
    async def update_miner(db: AsyncSession, miner_id: str, name: Optional[str] = None) -> dict:
        """Update miner details (currently only name)."""
        miner = await MinerDBService.get_miner_by_id(db, miner_id)
        if not miner:
            return {"success": False, "error": "Miner not found"}
        
        if name is not None:
            miner.name = name
        
        try:
            db.add(miner)
            await db.commit()
            await db.refresh(miner)
        except Exception as e:
            await db.rollback()
            logger.error(f"Database error updating miner {miner_id}: {e}")
            return {"success": False, "error": "Database error"}
        
        return {"success": True, "miner": miner.to_dict()}
    
    @staticmethod
    async def delete_miner(db: AsyncSession, miner_id: str) -> dict:
        """Delete a miner from the database."""
        miner = await MinerDBService.get_miner_by_id(db, miner_id)
        if not miner:
            return {"success": False, "error": "Miner not found"}
        
        ip = miner.ip
        await db.delete(miner)
        await db.commit()  # Commit immediately to persist deletion
        
        logger.info(f"Deleted miner device: {ip}")
        
        return {"success": True, "message": f"Miner {ip} deleted successfully"}
    
    @staticmethod
    async def refresh_miner(db: AsyncSession, miner_id: str) -> dict:
        """Refresh a single miner's data from the device."""
        miner = await MinerDBService.get_miner_by_id(db, miner_id)
        if not miner:
            return {"success": False, "error": "Miner not found"}
        
        return await MinerDBService._update_miner_data(db, miner)
    
    @staticmethod
    async def _update_miner_data(db: AsyncSession, miner: MinerDevice) -> dict:
        """Internal method to fetch and update miner data from device."""
        result = await MinerService.get_miner_data(miner.ip)
        
        if not result.get("success"):
            miner.is_online = False
            miner.last_error = result.get("error", "Failed to connect")
            db.add(miner)  
            await db.commit() 
            await db.refresh(miner)
            return {
                "success": False,
                "ip": miner.ip,
                "error": result.get("error"),
                "miner": miner.to_dict()
            }
        
        # Update all fields from fresh data
        data = result["data"]
        miner.hostname = data.get("hostname")
        miner.mac = data.get("mac")
        miner.make = data.get("make")
        miner.model = data.get("model")
        miner.firmware = data.get("firmware")
        miner.hashrate_current = data.get("hashrate_current")
        miner.hashrate_avg = data.get("hashrate_avg")
        miner.expected_hashrate = data.get("expected_hashrate")
        miner.temperature = data.get("temperature")
        miner.temperature_max = data.get("temperature_max")
        miner.vr_temperature = data.get("vr_temperature")
        miner.power_usage = data.get("power_usage")
        miner.power_limit = data.get("power_limit")
        miner.efficiency = data.get("efficiency")
        miner.voltage = data.get("voltage")
        miner.fan_speeds = data.get("fan_speeds", [])
        miner.chip_count = data.get("chip_count")
        miner.is_mining = data.get("is_mining")
        miner.errors = data.get("errors", [])
        miner.uptime = data.get("uptime")
        
        # Handle pools
        pools_data = []
        for pool in data.get("pools", []):
            if isinstance(pool, dict):
                pools_data.append(pool)
            else:
                pools_data.append(pool.model_dump() if hasattr(pool, 'model_dump') else dict(pool))
        miner.pools = pools_data
        miner.primary_pool = data.get("primary_pool", "No Pool")
        
        miner.api_version = data.get("api_version")
        miner.is_online = True
        miner.last_error = None
        miner.last_seen = datetime.now(timezone.utc)
        
        db.add(miner) 
        await db.commit()  
        await db.refresh(miner)
        
        return {
            "success": True,
            "ip": miner.ip,
            "miner": miner.to_dict()
        }
    
    @staticmethod
    async def refresh_all_miners(db: AsyncSession) -> dict:
        """Refresh data for all stored miners in parallel."""
        miners = await MinerDBService.get_all_miners(db)
        
        if not miners:
            return {"total": 0, "success": 0, "failed": 0, "miners": []}
        
        # Parallel refresh for better performance
        tasks = [MinerDBService._update_miner_data(db, miner) for miner in miners]
        results_list = await asyncio.gather(*tasks, return_exceptions=True)
        
        results = {"total": len(miners), "success": 0, "failed": 0, "miners": []}
        
        for result in results_list:
            if isinstance(result, Exception):
                results["failed"] += 1
                results["miners"].append({"success": False, "error": str(result)})
            elif result.get("success"):
                results["success"] += 1
                results["miners"].append(result)
            else:
                results["failed"] += 1
                results["miners"].append(result)
        
        logger.info(f"Refreshed {results['success']}/{results['total']} miners successfully")
        
        return results
