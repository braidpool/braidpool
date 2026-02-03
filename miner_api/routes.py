from fastapi import APIRouter, Depends, Query, HTTPException, status
from fastapi.security import APIKeyHeader
from datetime import datetime
from typing import List, Optional
from pydantic import BaseModel
from .models import MinerData as MinerDataModel, PoolInfo
from .services import MinerService
from .config import settings
from . import __version__
import logging

logger = logging.getLogger("miner_api")
router = APIRouter()

# Simple API key auth
api_key_header = APIKeyHeader(name="X-API-Key", auto_error=False)

async def verify_api_key(api_key: str = Depends(api_key_header)) -> str:
    """Verify API key if configured."""
    if not settings.API_KEY:
        return "no-auth"
    if not api_key:
        raise HTTPException(status_code=401, detail="Missing API Key")
    if api_key != settings.API_KEY:
        raise HTTPException(status_code=403, detail="Invalid API Key")
    return api_key


# Request/Response models
class HealthResponse(BaseModel):
    status: str
    version: str
    timestamp: datetime


# Endpoints
@router.get("/health", response_model=HealthResponse, tags=["health"])
async def health_check():
    """Health check endpoint."""
    return HealthResponse(status="healthy", version=__version__, timestamp=datetime.utcnow())


@router.get("/miners/live", tags=["miners"])
async def get_miner_data_live(
    ip: str = Query(..., description="IP address"),
    _: str = Depends(verify_api_key)
):
    """Query miner directly in real-time."""
    result = await MinerService.get_miner_data(ip)
    return result



