from typing import List
import os

class Settings:
    # Server settings
    HOST: str = "0.0.0.0"
    PORT: int = 5001
    RELOAD: bool = False
    ALLOWED_ORIGINS: List[str] = [
        "http://localhost:3000",
        "http://localhost:3001",
    ]
    MINER_TIMEOUT: int = 10  # seconds
    LOG_LEVEL: str = "INFO"
    
    # Database settings
    DATABASE_URL: str = os.getenv(
        "DATABASE_URL", 
        "sqlite+aiosqlite:///./miner_api.db"
    )
    DATABASE_ECHO: bool = False  # Set True to log SQL queries
    
    MINER_REFRESH_ENABLED: bool = True
    MINER_REFRESH_INTERVAL: int = 60  # seconds 

settings = Settings()
