CREATE TABLE IF NOT EXISTS miner_devices (
    id          TEXT PRIMARY KEY NOT NULL,
    ip          TEXT NOT NULL UNIQUE,
    name        TEXT,

    -- Device identification
    hostname    TEXT,
    mac         TEXT,
    make        TEXT,
    model       TEXT,
    firmware    TEXT,

    -- Performance metrics
    hashrate_current  REAL,
    hashrate_avg      REAL,
    expected_hashrate REAL,

    -- Temperature readings
    temperature      REAL,
    temperature_max  REAL,
    vr_temperature   REAL,

    -- Power metrics
    power_usage  INTEGER,
    power_limit  INTEGER,
    efficiency   REAL,
    voltage      REAL,

    -- Hardware status 
    fan_speeds  TEXT NOT NULL DEFAULT '[]',
    chip_count  INTEGER,
    is_mining   INTEGER,
    errors      TEXT NOT NULL DEFAULT '[]',
    uptime      INTEGER,

    -- Pool information 
    pools        TEXT NOT NULL DEFAULT '[]',
    primary_pool TEXT NOT NULL DEFAULT 'No Pool',

    -- API info
    api_version TEXT,

    -- Connection status
    is_online  INTEGER NOT NULL DEFAULT 0,
    last_error TEXT,

    -- Timestamps
    created_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%SZ', 'now')),
    updated_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%SZ', 'now')),
    last_seen  TEXT
);

CREATE INDEX IF NOT EXISTS idx_miner_devices_ip ON miner_devices(ip);
