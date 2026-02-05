from fastapi import APIRouter, Depends, Query, HTTPException, status
from fastapi.security import APIKeyHeader
from pydantic import BaseModel
from ipaddress import ip_address, AddressValueError
from .services import MinerService
from .config import settings
from . import __version__
import logging
from datetime import datetime, timezone

logger = logging.getLogger("miner_api")
router = APIRouter()

# Simple API key auth
api_key_header = APIKeyHeader(name="X-API-Key", auto_error=False)

def validate_ip_address(ip: str) -> str:
    try:
        ip_address(ip)
        return ip
    except AddressValueError:
        raise HTTPException(status_code=400, detail="Invalid IP address format")


# Request/Response models
class HealthResponse(BaseModel):
    status: str
    version: str
    timestamp: datetime


# Endpoints
@router.get("/health", response_model=HealthResponse, tags=["health"])
async def health_check():
    """Health check endpoint."""
    return HealthResponse(status="healthy", version=__version__, timestamp=datetime.now(timezone.utc))


@router.get("/miners/live", tags=["miners"])
async def get_miner_data_live(
    ip: str = Query(..., description="IP address"),   
):
    """Query miner directly in real-time."""
    validated_ip = validate_ip_address(ip)
    result = await MinerService.get_miner_data(validated_ip)
    return result
