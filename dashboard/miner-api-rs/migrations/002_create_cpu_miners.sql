CREATE TABLE IF NOT EXISTS cpu_miners (
    id         TEXT PRIMARY KEY NOT NULL,
    api_url    TEXT NOT NULL UNIQUE,
    label      TEXT,

    is_online  INTEGER NOT NULL DEFAULT 0,
    last_stats TEXT,
    last_seen  TEXT,

    created_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%SZ', 'now')),
    updated_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%SZ', 'now'))
);
