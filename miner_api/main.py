from fastapi import FastAPI, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from contextlib import asynccontextmanager
import time
import uuid
import logging
import sys
import asyncio
from .config import settings
from .routes import router
from .database import init_db, close_db, async_session_factory
from .db_services import MinerDBService
from . import __version__

# Setup logging
logging.basicConfig(
    level=getattr(logging, settings.LOG_LEVEL.upper()),
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    stream=sys.stdout
)
logger = logging.getLogger("miner_api")

_refresh_task = None


async def periodic_miner_refresh():
    while True:
        try:
            await asyncio.sleep(settings.MINER_REFRESH_INTERVAL)
            
            async with async_session_factory() as db:
                try:
                    result = await MinerDBService.refresh_all_miners(db)
                    logger.debug(
                        f"Periodic refresh: {result['success']}/{result['total']} miners updated"
                    )
                except Exception as e:
                    await db.rollback()
                    logger.error(f"Error during periodic refresh: {e}")
                    
        except asyncio.CancelledError:
            logger.info("Periodic refresh task cancelled")
            break
        except Exception as e:
            logger.error(f"Unexpected error in periodic refresh: {e}")
            await asyncio.sleep(60)  

@asynccontextmanager
async def lifespan(app: FastAPI):
    global _refresh_task
    
    logger.info(f"Starting Miner API v{__version__}")
    logger.info(f"Config: Host={settings.HOST}, Port={settings.PORT}")
    
    # Initialize database
    await init_db()
    logger.info(f"Database initialized: {settings.DATABASE_URL}")
    
    # Start background refresh task
    if settings.MINER_REFRESH_ENABLED:
        _refresh_task = asyncio.create_task(periodic_miner_refresh())
        logger.info(f"Background refresh enabled (interval: {settings.MINER_REFRESH_INTERVAL}s)")
    
    yield
    
    # Cleanup
    if _refresh_task:
        _refresh_task.cancel()
        try:
            await _refresh_task
        except asyncio.CancelledError:
            pass
    
    await close_db()
    logger.info("Shutting down")


app = FastAPI(
    title="Braidpool Miner API",
    description="API for managing and monitoring Bitcoin mining hardware",
    version=__version__,
    lifespan=lifespan,
    docs_url="/docs",
    redoc_url="/redoc",
)

# CORS configuration
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.ALLOWED_ORIGINS,
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "DELETE"],
    allow_headers=["*"],
    expose_headers=["X-Request-ID"],
)


@app.middleware("http")
async def add_request_id(request: Request, call_next):
    request_id = str(uuid.uuid4())
    request.state.request_id = request_id
    
    start_time = time.time()
    response = await call_next(request)
    duration = (time.time() - start_time) * 1000
    
    logger.info(f"{request.method} {request.url.path} - {response.status_code} ({duration:.0f}ms)")
    response.headers["X-Request-ID"] = request_id
    
    return response


@app.exception_handler(Exception)
async def global_exception_handler(request: Request, exc: Exception):
    request_id = getattr(request.state, "request_id", "unknown")
    logger.error(f"Unhandled exception: {str(exc)}", exc_info=True)
    
    return JSONResponse(
        status_code=500,
        content={"detail": "Internal server error", "request_id": request_id}
    )


# Include API routes
app.include_router(router, prefix="/api")
