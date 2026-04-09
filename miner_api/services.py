from typing import Optional, Tuple, List
import urllib.parse
import asyncio
import logging
from pyasic import get_miner
from .models import MinerData, PoolInfo
from .config import settings

logger = logging.getLogger("miner_api")


class MinerService:
    @staticmethod
    def _safe_int(val) -> Optional[int]:
        try:
            return int(float(val)) if val is not None else None
        except Exception:
            return None
    
    @staticmethod
    def _safe_float(val) -> Optional[float]:
        try:
            return round(float(val), 2) if val is not None else None
        except Exception:
            return None
    
    @staticmethod
    def _extract_temperatures(data) -> Tuple[Optional[float], Optional[float], Optional[float]]:
        temperature = None
        temperature_max = None
        vr_temperature = None
        
        hashboards = getattr(data, 'hashboards', [])
        if hashboards:
            asic_temps = []
            vr_temps = []
            
            for board in hashboards:
                if getattr(board, 'chip_temp', None) is not None:
                    asic_temps.append(board.chip_temp)
                if getattr(board, 'temp', None) is not None:
                    vr_temps.append(board.temp)
            
            if asic_temps:
                temperature = MinerService._safe_float(sum(asic_temps) / len(asic_temps))
                temperature_max = MinerService._safe_float(max(asic_temps))
            elif vr_temps:
                temperature = MinerService._safe_float(vr_temps[0])
            
            if vr_temps:
                vr_temperature = MinerService._safe_float(sum(vr_temps) / len(vr_temps))
        
        # Fallback temperature sources
        if temperature is None and hasattr(data, 'temperature_avg'):
            temperature = MinerService._safe_float(getattr(data, 'temperature_avg'))
        if temperature is None and hasattr(data, 'env_temp'):
            temperature = MinerService._safe_float(getattr(data, 'env_temp'))
        
        return temperature, temperature_max, vr_temperature
    
    @staticmethod
    def _extract_fans(data) -> List[int]:
        fans = getattr(data, 'fans', [])
        fan_speeds = [
            MinerService._safe_int(fan.speed)
            for fan in fans
            if getattr(fan, 'speed', None) is not None
        ]
        # Filter out any None values returned by _safe_int to satisfy List[int] typing
        return [speed for speed in fan_speeds if speed is not None]
    
    @staticmethod
    def _validate_pool_info(pool_info: PoolInfo) -> None:
        """Validate pool info and mark as invalid if missing required fields."""
        if not pool_info.url or not pool_info.user:
            pool_info.status = "invalid"
    
    @staticmethod
    def _extract_pools(data) -> List[PoolInfo]:
        """Extract pool configuration from miner response."""
        pools_data = []
        
        # Primary pool source
        pools = getattr(data, 'pools', [])
        for pool in pools:
            pool_info = PoolInfo(
                url=str(pool.url) if getattr(pool, 'url', None) else None,
                user=getattr(pool, 'user', None),
                status=getattr(pool, 'status', None)
            )
            MinerService._validate_pool_info(pool_info)
            pools_data.append(pool_info)
        
        # Fallback to config pools if none found
        if not pools_data:
            config = getattr(data, 'config', None)
            if config and getattr(config, 'pools', None):
                pool_config = config.pools
                if hasattr(pool_config, 'groups'):
                    for group in pool_config.groups:
                        if hasattr(group, 'pools'):
                            for pool in group.pools:
                                pool_info = PoolInfo(
                                    url=str(pool.url) if getattr(pool, 'url', None) else None,
                                    user=getattr(pool, 'user', None),
                                    status="configured"
                                )
                                MinerService._validate_pool_info(pool_info)
                                pools_data.append(pool_info)
        
        return pools_data
    
    @staticmethod
    def _extract_primary_pool(pools_data: List[PoolInfo]) -> str:
        valid_pools = [p for p in pools_data if p.status != "invalid" and p.url]
        
        if not valid_pools:
            return "No Pool"
        
        try:
            url = valid_pools[0].url
            parsed = urllib.parse.urlparse(
                url if url.startswith(('http', 'stratum')) else f'stratum+tcp://{url}'
            )
            if parsed.hostname:
                return parsed.hostname.replace('www.', '').split('.')[0].title()
        except Exception as e:
            logger.warning(f"Failed to parse primary pool URL: {e}")
        
        return "Unknown Pool"
    
    @staticmethod
    def normalize_miner_data(raw_data) -> MinerData:
        temperature, temperature_max, vr_temperature = MinerService._extract_temperatures(raw_data)
        fan_speeds = MinerService._extract_fans(raw_data)
        pools_data = MinerService._extract_pools(raw_data)
        primary_pool = MinerService._extract_primary_pool(pools_data)
        raw_hashrate = getattr(raw_data, "raw_hashrate", None)
        hashrate = getattr(raw_data, "hashrate", None)
        expected_hashrate = getattr(raw_data, "expected_hashrate", None)
        
        return MinerData(
            ip=getattr(raw_data, "ip", None),
            hostname=getattr(raw_data, "hostname", None),
            mac=getattr(raw_data, "mac", None),
            make=getattr(raw_data, "make", None),
            model=getattr(raw_data, "model", None),
            firmware=getattr(raw_data, "fw_ver", None),
            hashrate_current=MinerService._safe_float(raw_hashrate.rate if raw_hashrate else None),
            hashrate_avg=MinerService._safe_float(hashrate.rate if hashrate else None),
            expected_hashrate=MinerService._safe_float(expected_hashrate.rate if expected_hashrate else None),
            temperature=temperature,
            temperature_max=temperature_max,
            vr_temperature=vr_temperature,
            power_usage=MinerService._safe_int(getattr(raw_data, "wattage", None)),
            power_limit=MinerService._safe_int(getattr(raw_data, "wattage_limit", None)) 
                if hasattr(raw_data, "wattage_limit") else None,
            efficiency=MinerService._safe_float(getattr(raw_data, "efficiency_fract", None)),
            voltage=MinerService._safe_float(getattr(raw_data, "voltage", None)) 
                if hasattr(raw_data, "voltage") else None,
            fan_speeds=fan_speeds,
            chip_count=MinerService._safe_int(getattr(raw_data, "total_chips", None)),
            is_mining=getattr(raw_data, "is_mining", None),
            errors=[str(err) for err in getattr(raw_data, "errors", [])],
            uptime=MinerService._safe_int(getattr(raw_data, "uptime", None)),
            pools=pools_data,
            primary_pool=primary_pool,
            api_version=getattr(raw_data, "api_ver", None),
            timestamp=getattr(raw_data, "timestamp", None),
        )
    
    @staticmethod
    async def get_miner_data(ip: str) -> dict:
        """Retrieve and normalize data from a miner at the specified IP address."""
        try:
            # Add timeout to prevent hanging connections
            miner = await asyncio.wait_for(
                get_miner(ip),
                timeout=settings.MINER_TIMEOUT
            )
            
            # Check if miner was detected
            if miner is None:
                logger.warning(f"Miner not detected or unsupported model: {ip}")
                return {
                    "success": False,
                    "ip": ip,
                    "error": "Miner not detected or unsupported model"
                }
            
            raw_data = await asyncio.wait_for(
                miner.get_data(),
                timeout=settings.MINER_TIMEOUT
            )
            
            normalized_data = MinerService.normalize_miner_data(raw_data)
            
            logger.info(f"Successfully retrieved data from miner {ip} (model: {normalized_data.model})")
            
            return {
                "success": True,
                "ip": ip,
                "data": normalized_data.model_dump()
            }
            
        except asyncio.TimeoutError:
            error_msg = f"Connection timeout after {settings.MINER_TIMEOUT}s"
            logger.warning(f"Timeout connecting to miner {ip}")
            return {"success": False, "ip": ip, "error": error_msg}
        
        except ConnectionRefusedError:
            error_msg = "Connection refused - miner may be offline or unreachable"
            logger.warning(f"Connection refused by miner {ip}")
            return {"success": False, "ip": ip, "error": error_msg}
        
        except Exception as e:
            error_msg = f"Failed to connect to miner: {str(e)}"
            logger.error(f"Unexpected error retrieving miner data from {ip}: {e}", exc_info=True)
            return {"success": False, "ip": ip, "error": error_msg}
