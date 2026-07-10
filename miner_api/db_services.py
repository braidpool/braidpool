import asyncio
from typing import Optional, List
from sqlalchemy import select
from sqlalchemy.exc import IntegrityError
from sqlalchemy.ext.asyncio import AsyncSession
from datetime import datetime, timezone
import logging

from .db_models import MinerDevice
from .services import MinerService

logger = logging.getLogger("miner_api")


def _normalize_mac(mac: Optional[str]) -> Optional[str]:
    if not mac:
        return None
    return mac.strip().lower().replace("-", ":")


def _apply_device_fields(miner: MinerDevice, data: dict) -> None:
    miner.hostname = data.get("hostname")
    miner.mac = _normalize_mac(data.get("mac"))
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
    
    # pools info 
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


class MinerDBService:
    
    @staticmethod
    async def add_miner(db: AsyncSession, ip: str, name: Optional[str] = None) -> dict:
        """Add a new miner device to the database and fetch its initial data."""
        result = await MinerService.get_miner_data(ip)
        if not result.get("success"):
            existing_by_ip = await MinerDBService.get_miner_by_ip(db, ip)
            if existing_by_ip:
                return {
                    "success": False,
                    "error": f"Miner with IP {ip} already exists",
                    "already_exists": True,
                    "miner": existing_by_ip.to_dict(),
                }
            miner = MinerDevice(
                ip=ip,
                name=name,
                is_online=False,
                last_error=result.get("error", "Failed to connect"),
            )
            db.add(miner)
            try:
                await db.commit()
            except Exception as e:
                await db.rollback()
                logger.error(f"Database error adding offline miner {ip}: {e}")
                return {"success": False, "error": "Database error adding miner", "db_error": True}
            await db.refresh(miner)
            logger.info(f"Added offline miner device: {ip}")
            return {
                "success": True,
                "warning": "Miner added but currently offline",
                "miner": miner.to_dict(),
            }
        data = result["data"]
        mac = _normalize_mac(data.get("mac"))
        if not mac:
            logger.error(f"Device at {ip} did not report a MAC address; cannot add miner.")
            return {"success": False, "error": "Device did not report a MAC address"}

        data["mac"] = mac
        existing = await MinerDBService.get_miner_by_mac(db, mac)
        if existing:
            old_ip = existing.ip
            existing.ip = ip
            if name is not None:
                existing.name = name
            _apply_device_fields(existing, data)
            db.add(existing)
            try:
                await db.commit()
                await db.refresh(existing)
            except Exception as e:
                await db.rollback()
                logger.error(f"Database error updating miner MAC {mac}: {e}")
                return {"success": False, "error": "Database error updating miner", "db_error": True}
            if old_ip != ip:
                logger.info(f"Miner MAC {mac} IP updated from {old_ip} to {ip}, record updated.")
            return {"success": True, "miner": existing.to_dict()}

        miner = MinerDevice.from_miner_data(ip, data, name=name)
        db.add(miner)
        try:
            await db.commit()
        except IntegrityError:
            await db.rollback()
            existing = await MinerDBService.get_miner_by_mac(db, mac)
            return {
                "success": False,
                "error": f"Miner with MAC {mac} already exists",
                "already_exists": True,
                "miner": existing.to_dict() if existing else None,
            }
        await db.refresh(miner)

        logger.info(f"Added new miner device: {ip} (model: {miner.model})")

        return {"success": True, "miner": miner.to_dict()}
    
    @staticmethod
    async def get_miner_by_ip(db: AsyncSession, ip: str) -> Optional[MinerDevice]:
        """Get a miner by IP address. Returns the first match; IP is no longer unique."""
        result = await db.execute(
            select(MinerDevice).where(MinerDevice.ip == ip)
        )
        return result.scalars().first()
    @staticmethod
    async def get_miner_by_mac(db: AsyncSession, mac: str) -> Optional[MinerDevice]:
        result = await db.execute(
            select(MinerDevice).where(MinerDevice.mac == mac)
        )
        rows = result.scalars().all()
        if not rows:
            return None
        if len(rows) > 1:
            logger.warning(
                f"Multiple rows found for MAC {mac}; returning first match to allow recovery"
            )
        return rows[0]

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
        miner = await MinerDBService.get_miner_by_id(db, miner_id)
        if not miner:
            return {"success": False, "error": "Miner not found", "not_found": True}
        
        if name is not None:
            miner.name = name
        
        try:
            db.add(miner)
            await db.commit()
            await db.refresh(miner)
        except Exception as e:
            await db.rollback()
            logger.error(f"Database error updating miner {miner_id}: {e}")
            return {"success": False, "error": "Database error", "db_error": True}
        
        return {"success": True, "miner": miner.to_dict()}
    
    @staticmethod
    async def delete_miner(db: AsyncSession, miner_id: str) -> dict:
        miner = await MinerDBService.get_miner_by_id(db, miner_id)
        if not miner:
            return {"success": False, "error": "Miner not found", "not_found": True}
        
        ip = miner.ip
        try:
            await db.delete(miner)
            await db.commit()
        except Exception as e:
            await db.rollback()
            logger.error(f"Database error deleting miner {miner_id}: {e}")
            return {"success": False, "error": "Database error", "db_error": True}
        
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
        
        _apply_device_fields(miner, result["data"])
        
        db.add(miner) 
        await db.commit()  
        await db.refresh(miner)
        
        return {
            "success": True,
            "ip": miner.ip,
            "miner": miner.to_dict()
        }
    
    @staticmethod
    async def _apply_device_data(db: AsyncSession, miner: MinerDevice, device_result: dict) -> dict:
        if not device_result.get("success"):
            miner.is_online = False
            miner.last_error = device_result.get("error", "Failed to connect")
            db.add(miner)
            return {
                "success": False,
                "ip": miner.ip,
                "error": device_result.get("error"),
                "miner": miner.to_dict()
            }
        
        _apply_device_fields(miner, device_result["data"])
        
        db.add(miner)
        
        return {
            "success": True,
            "ip": miner.ip,
            "miner": miner.to_dict()
        }
    
    @staticmethod
    async def refresh_all_miners(db: AsyncSession) -> dict:
        miners = await MinerDBService.get_all_miners(db)
        
        if not miners:
            return {"total": 0, "success": 0, "failed": 0, "miners": []}
        
        # Fetch device data in parallel (no DB involvement)
        async def fetch_device_data(miner: MinerDevice) -> tuple[MinerDevice, dict]:
            """Fetch data from device without touching DB."""
            try:
                result = await MinerService.get_miner_data(miner.ip)
                return (miner, result)
            except Exception as e:
                return (miner, {"success": False, "error": str(e)})
        
        tasks = [fetch_device_data(miner) for miner in miners]
        fetch_results = await asyncio.gather(*tasks, return_exceptions=True)
        
        results = {"total": len(miners), "success": 0, "failed": 0, "miners": []}
        
        for fetch_result in fetch_results:
            if isinstance(fetch_result, Exception):
                results["failed"] += 1
                results["miners"].append({"success": False, "error": str(fetch_result)})
                continue
            
            miner, device_result = fetch_result
            update_result = await MinerDBService._apply_device_data(db, miner, device_result)
            
            if update_result.get("success"):
                results["success"] += 1
            else:
                results["failed"] += 1
            results["miners"].append(update_result)
        await db.commit()
        
        logger.info(f"Refreshed {results['success']}/{results['total']} miners successfully")
        
        return results
