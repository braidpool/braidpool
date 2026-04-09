from typing import List

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

settings = Settings()
