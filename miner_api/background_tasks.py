import asyncio
from .config import settings
import logging

logger = logging.getLogger("miner_api")

class MinerPollingService:
    def __init__(self):
        self._task = None
        self._running = False
    
    async def start(self):
        if self._running:
            logger.warning("Polling service already running")
            return
        self._running = True
        self._task = asyncio.create_task(self._polling_loop())
        logger.info(f"Polling service started (interval: {settings.POLL_INTERVAL} s)")
    
    async def stop(self):
        if not self._running:
            return
        self._running = False
        if self._task:
            self._task.cancel()
            try:
                await self._task
            except asyncio.CancelledError:
                pass
        logger.info("Miner polling service stopped")
    
    async def _polling_loop(self):
        while self._running:
            try:
                # Polling loop removed - no database to store results
                logger.debug("Polling service running (no miners to poll without database)")
                await asyncio.sleep(settings.POLL_INTERVAL)
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"Error in polling loop: {e}", exc_info=True)
                await asyncio.sleep(5)

polling_service = MinerPollingService()
