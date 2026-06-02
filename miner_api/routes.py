from fastapi import APIRouter, HTTPException, status, Depends
from pydantic import BaseModel, Field
from ipaddress import ip_address, AddressValueError
from sqlalchemy.ext.asyncio import AsyncSession
from typing import Optional, List
from .database import get_db
from .db_services import MinerDBService
from . import __version__
import logging
from datetime import datetime, timezone

logger = logging.getLogger("miner_api")
router = APIRouter()


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


class AddMinerRequest(BaseModel):
    """Request model for adding a miner device."""
    ip: str = Field(..., description="IP address of the miner")
    name: Optional[str] = Field(None, description="User-defined name for the miner")


class UpdateMinerRequest(BaseModel):
    """Request model for updating a miner device."""
    name: Optional[str] = Field(None, description="User-defined name for the miner")


class MinerResponse(BaseModel):
    """Response model for miner data."""
    success: bool
    miner: Optional[dict] = None
    error: Optional[str] = None
    warning: Optional[str] = None


class MinersListResponse(BaseModel):
    """Response model for list of miners."""
    success: bool
    count: int
    miners: List[dict]


class RefreshResponse(BaseModel):
    """Response model for refresh operations."""
    total: int
    success: int
    failed: int
    miners: List[dict]


# Endpoints
@router.get("/health", response_model=HealthResponse, tags=["health"])
async def health_check():
    """Health check endpoint."""
    return HealthResponse(status="healthy", version=__version__, timestamp=datetime.now(timezone.utc))


@router.post("/miners", response_model=MinerResponse, tags=["miners-db"])
async def add_miner(
    request: AddMinerRequest,
    db: AsyncSession = Depends(get_db)
):
    
    validated_ip = validate_ip_address(request.ip)
    result = await MinerDBService.add_miner(db, validated_ip, request.name)
    
    if not result.get("success") and "already exists" in result.get("error", ""):
        raise HTTPException(
            status_code=status.HTTP_409_CONFLICT,
            detail=result
        )
    
    return result


@router.get("/miners", response_model=MinersListResponse, tags=["miners-db"])
async def get_all_miners(db: AsyncSession = Depends(get_db)):
    """Get all stored miner devices with their latest cached data."""
    miners = await MinerDBService.get_all_miners(db)
    return {
        "success": True,
        "count": len(miners),
        "miners": [miner.to_dict() for miner in miners]
    }


@router.get("/miners/{miner_id}", response_model=MinerResponse, tags=["miners-db"])
async def get_miner(miner_id: str, db: AsyncSession = Depends(get_db)):
    """Get a specific miner by ID."""
    miner = await MinerDBService.get_miner_by_id(db, miner_id)
    if not miner:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail={"success": False, "error": "Miner not found"}
        )
    return {"success": True, "miner": miner.to_dict()}


@router.put("/miners/{miner_id}", response_model=MinerResponse, tags=["miners-db"])
async def update_miner(
    miner_id: str,
    request: UpdateMinerRequest,
    db: AsyncSession = Depends(get_db)
):
    """Update miner details (e.g., name)."""
    result = await MinerDBService.update_miner(db, miner_id, request.name)
    if not result.get("success"):
        if result.get("not_found"):
            raise HTTPException(
                status_code=status.HTTP_404_NOT_FOUND,
                detail=result
            )
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail=result
        )
    return result


@router.delete("/miners/{miner_id}", tags=["miners-db"])
async def delete_miner(miner_id: str, db: AsyncSession = Depends(get_db)):
    """Remove a miner device from the database."""
    result = await MinerDBService.delete_miner(db, miner_id)
    if not result.get("success"):
        if result.get("not_found"):
            raise HTTPException(
                status_code=status.HTTP_404_NOT_FOUND,
                detail=result
            )
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail=result
        )
    return result


@router.post("/miners/{miner_id}/refresh", response_model=MinerResponse, tags=["miners-db"])
async def refresh_miner(miner_id: str, db: AsyncSession = Depends(get_db)):
    """Refresh data for a specific miner from the device."""
    result = await MinerDBService.refresh_miner(db, miner_id)
    if "error" in result and result.get("error") == "Miner not found":
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail=result
        )
    return result


@router.post("/miners/refresh/all", response_model=RefreshResponse, tags=["miners-db"])
async def refresh_all_miners(db: AsyncSession = Depends(get_db)):
    """Refresh data for all stored miners from their devices."""
    return await MinerDBService.refresh_all_miners(db)
