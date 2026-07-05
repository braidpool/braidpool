from sqlalchemy.ext.asyncio import create_async_engine, AsyncSession, async_sessionmaker
from sqlalchemy.orm import declarative_base
from typing import AsyncGenerator
import logging


from .config import settings

logger = logging.getLogger("miner_api")


def _build_engine_kwargs() -> dict:
    kwargs = {
        "echo": settings.DATABASE_ECHO,
    }
    if settings.DATABASE_URL.startswith("sqlite"):
        kwargs["connect_args"] = {"check_same_thread": False}
    return kwargs


engine = create_async_engine(
    settings.DATABASE_URL,
    **_build_engine_kwargs(),
)

async_session_factory = async_sessionmaker(
    engine,
    class_=AsyncSession,
    expire_on_commit=False,
    autoflush=False,
)

Base = declarative_base()

async def get_db() -> AsyncGenerator[AsyncSession, None]:
    """Dependency to get database session."""
    async with async_session_factory() as session:
        try:
            yield session
        except Exception:
            await session.rollback()
            raise


async def init_db():
    """Initialize database and create all tables."""
    async with engine.begin() as conn:
        from . import db_models
        await conn.run_sync(Base.metadata.create_all)
    logger.info(f"Database initialized: {settings.DATABASE_URL}")


async def close_db():
    """Close database connections."""
    await engine.dispose()
    logger.info("Database connections closed")
