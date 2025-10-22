-- 1. Bead
CREATE TABLE Bead (
    id                  INTEGER PRIMARY KEY AUTOINCREMENT,
    hash                TEXT NOT NULL CHECK (hash REGEXP '^[0-9A-Fa-f]{64}$'),
    -- Block header fields
    nVersion            TEXT NOT NULL CHECK (nVersion REGEXP '^[0-9A-Fa-f]{8}$'),
    hashPrevBlock       TEXT NOT NULL CHECK (hashPrevBlock REGEXP '^[0-9A-Fa-f]{64}$'),
    hashMerkleRoot      TEXT NOT NULL CHECK (hashMerkleRoot REGEXP '^[0-9A-Fa-f]{64}$'),
    nTime               TEXT NOT NULL CHECK (nTime REGEXP '^[0-9A-Fa-f]{8}$'),
    nBits               TEXT NOT NULL CHECK (nBits REGEXP '^[0-9A-Fa-f]{8}$'),
    nNonce              TEXT NOT NULL CHECK (nNonce REGEXP '^[0-9A-Fa-f]{8}$'),
    -- Committed Metadata
    payout_address      TEXT NOT NULL CHECK (length(payout_address) <= 128),
    start_timestamp     INTEGER NOT NULL,           -- 64-bit unix epoch in MICROseconds
    comm_pub_key        TEXT NOT NULL CHECK (length(comm_pub_key) <= 512),
    min_target          TEXT NOT NULL CHECK (
        min_target REGEXP '^[0-9A-Fa-f]{8}$'
    ),
    weak_target         TEXT NOT NULL CHECK (       -- hex compact target
        weak_target REGEXP '^[0-9A-Fa-f]{8}$'
    ),
    miner_ip            TEXT NOT NULL CHECK (length(miner_ip) <= 45),
    -- UnCommitted Metadata
    extra_nonce         TEXT NOT NULL CHECK (extra_nonce REGEXP '^[0-9A-Fa-f]{16}$'),
    broadcast_timestamp INTEGER NOT NULL,       -- 64-bit unix epoch in MICROseconds
    signature           TEXT NOT NULL,
    -- Constraints
    UNIQUE (nVersion, hashPrevBlock, hashMerkleRoot, nTime, nBits, nNonce),
    UNIQUE (hash)
);

-- 2. Transactions
CREATE TABLE Transactions (
      bead_id           INTEGER NOT NULL REFERENCES Bead(id),
      txid              TEXT NOT NULL CHECK (txid REGEXP '^[0-9A-Fa-f]{64}$'),
      UNIQUE (bead_id, txid)
);

-- 3. Cohorts
-- Auxiliary: positive cohort numbers (append a row for each new cohort)
-- Cohort metadata can be added here
CREATE TABLE CohortIds (
    id INTEGER PRIMARY KEY CHECK (id > 0)
);

-- Mapping: exactly one row per bead; cohort_id NULL means "unassigned"
CREATE TABLE Cohorts (
    bead_id INTEGER PRIMARY KEY,    -- the bead’s id from Bead
    cohort_id INTEGER,              -- NULL until known; else references CohortIds(id)
    FOREIGN KEY (bead_id) REFERENCES Bead(id),
    FOREIGN KEY (cohort_id) REFERENCES CohortIds(id)
);

-- Helpful index: fast to pull all beads in a cohort and to scan for NULLs
CREATE INDEX cohorts_by_cohortid ON Cohorts(cohort_id);

-- Quick view of beads still awaiting a cohort assignment
CREATE VIEW Orphans AS
SELECT b.id
FROM Bead b
LEFT JOIN Cohorts c ON c.bead_id = b.id
WHERE c.cohort_id IS NULL;

-- 4. Relatives (parent/child link)
CREATE TABLE Relatives (
    child  INTEGER NOT NULL REFERENCES Bead(id),
    parent INTEGER NOT NULL REFERENCES Bead(id),
    PRIMARY KEY (parent, child)
);

-- 5. Timestamps provided by beads witnessing when they saw ancestors
CREATE TABLE ParentTimestamps (
    parent      INTEGER NOT NULL REFERENCES Bead(id),
    child       INTEGER NOT NULL REFERENCES Bead(id),
    timestamp   INTEGER NOT NULL,               -- 64-bit unix epoch in MICROseconds
    PRIMARY KEY (parent, child),                -- exactly one timestamp per link
    FOREIGN KEY (parent, child) REFERENCES Relatives(parent, child)
);

-- 6. A table allowing beads to witness timestamps for non-parent ancestors
-- (Not used currently)
CREATE TABLE AncestorTimestamps (
    bead_id  INTEGER NOT NULL REFERENCES Bead(id), 
    ancestor INTEGER NOT NULL REFERENCES Bead(id),
    timestamp INTEGER NOT NULL,
    PRIMARY KEY (bead_id, ancestor)
);

-- 7. Fast look-up indices
CREATE INDEX bead_txids ON Transactions(bead_id);
CREATE INDEX parents ON Relatives(parent);
CREATE INDEX children ON Relatives(child);
CREATE INDEX bead_hash ON Bead(hash);
CREATE INDEX timestamps_parents ON ParentTimestamps(parent);
CREATE INDEX timestamps_children ON ParentTimestamps(child);
CREATE INDEX bead_start_timestamp ON Bead(start_timestamp);
CREATE INDEX parent_timestamps_timestamp ON ParentTimestamps(timestamp);

-- 8. WAL mode for append-only workloads
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
PRAGMA foreign_keys = ON;
