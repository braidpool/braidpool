"""
In-memory miner store.

Designed to be replaced by a real database (SQLite / PostgreSQL) in a later
iteration. All state lives in a plain dict keyed by miner ID so the agent
starts instantly in both development and CI without any external dependency.
"""

import uuid
from copy import deepcopy
from typing import Optional

from models import Miner, MinerCreate, MinerUpdate, MinerStatus, MinerType


class MinerStore:
    def __init__(self):
        self._miners: dict[str, Miner] = {}


    def seed_defaults(self):
        """
        Pre-populate the store with a representative set of miners that mirrors
        the mock data already shown in the dashboard UI. This gives contributors
        a working API from the moment the container starts — no manual setup.
        """
        defaults = [
            MinerCreate(
                name="Antminer S19",
                miner_type=MinerType.asic,
                location="Rack A, Unit 3",
                status=MinerStatus.online,
                hashrate_th=95.2,
                temp_c=65.0,
                efficiency_j_th=34.5,
                power_draw_w=3250,
                uptime_pct=99.7,
                last_seen="2 mins ago",
                alerts=0,
            ),
            MinerCreate(
                name="Antminer S19",
                miner_type=MinerType.asic,
                location="Rack A, Unit 4",
                status=MinerStatus.online,
                hashrate_th=94.8,
                temp_c=68.0,
                efficiency_j_th=33.9,
                power_draw_w=3270,
                uptime_pct=99.5,
                last_seen="1 min ago",
                alerts=0,
            ),
            MinerCreate(
                name="Whatsminer M30S",
                miner_type=MinerType.asic,
                location="Rack B, Unit 1",
                status=MinerStatus.warning,
                hashrate_th=82.5,
                temp_c=74.0,
                efficiency_j_th=38.2,
                power_draw_w=3420,
                uptime_pct=97.2,
                last_seen="5 mins ago",
                alerts=1,
            ),
            MinerCreate(
                name="Antminer S19",
                miner_type=MinerType.asic,
                location="Rack B, Unit 2",
                status=MinerStatus.offline,
                hashrate_th=None,
                temp_c=None,
                efficiency_j_th=None,
                power_draw_w=None,
                uptime_pct=85.3,
                last_seen="2 hrs ago",
                alerts=2,
            ),
            MinerCreate(
                name="Whatsminer M30S",
                miner_type=MinerType.asic,
                location="Rack B, Unit 3",
                status=MinerStatus.online,
                hashrate_th=93.1,
                temp_c=66.0,
                efficiency_j_th=34.7,
                power_draw_w=3290,
                uptime_pct=99.8,
                last_seen="3 mins ago",
                alerts=0,
            ),
            MinerCreate(
                name="Antminer S19 Pro",
                miner_type=MinerType.asic,
                location="Rack C, Unit 1",
                status=MinerStatus.online,
                hashrate_th=109.5,
                temp_c=63.0,
                efficiency_j_th=32.1,
                power_draw_w=3180,
                uptime_pct=99.9,
                last_seen="1 min ago",
                alerts=0,
            ),
            MinerCreate(
                name="Antminer S19 Pro",
                miner_type=MinerType.asic,
                location="Rack C, Unit 2",
                status=MinerStatus.online,
                hashrate_th=108.7,
                temp_c=64.0,
                efficiency_j_th=32.4,
                power_draw_w=3200,
                uptime_pct=99.8,
                last_seen="2 mins ago",
                alerts=0,
            ),
            MinerCreate(
                name="Antminer S19",
                miner_type=MinerType.asic,
                location="Rack C, Unit 3",
                status=MinerStatus.warning,
                hashrate_th=91.4,
                temp_c=72.0,
                efficiency_j_th=35.8,
                power_draw_w=3320,
                uptime_pct=98.5,
                last_seen="7 mins ago",
                alerts=1,
            ),

            MinerCreate(
                name="cpunet-node-0",
                miner_type=MinerType.cpu,
                location="localhost",
                status=MinerStatus.online,
                hashrate_th=0.000001, 
                temp_c=None,
                efficiency_j_th=None,
                power_draw_w=None,
                uptime_pct=100.0,
                last_seen="just now",
                alerts=0,
            ),
        ]

        for i, payload in enumerate(defaults, start=1):
            miner_id = f"miner-{i:03d}"
            self._miners[miner_id] = Miner(id=miner_id, **payload.model_dump())

    def all(self) -> list[Miner]:
        return list(self._miners.values())

    def get(self, miner_id: str) -> Optional[Miner]:
        return self._miners.get(miner_id)

    def create(self, payload: MinerCreate) -> Miner:
        miner_id = f"miner-{uuid.uuid4().hex[:8]}"
        miner = Miner(id=miner_id, **payload.model_dump())
        self._miners[miner_id] = miner
        return miner

    def update(self, miner_id: str, payload: MinerUpdate) -> Optional[Miner]:
        existing = self._miners.get(miner_id)
        if existing is None:
            return None
        updated_data = existing.model_dump()
        for field, value in payload.model_dump(exclude_unset=True).items():
            updated_data[field] = value
        self._miners[miner_id] = Miner(**updated_data)
        return self._miners[miner_id]

    def delete(self, miner_id: str) -> bool:
        if miner_id not in self._miners:
            return False
        del self._miners[miner_id]
        return True
