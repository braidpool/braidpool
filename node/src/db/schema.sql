-- 1. Bead
CREATE TABLE Bead (
    id                  INTEGER PRIMARY KEY ,
    hash                BLOB NOT NULL,
    -- Block header fields
    nVersion            INTEGER CHECK (nVersion >= 0 AND nVersion < 0x100000000),
    hashPrevBlock       BLOB NOT NULL,
    hashMerkleRoot      BLOB NOT NULL,
    nTime               INTEGER CHECK (nTime >= 0 AND nTime < 0x100000000),
    nBits               INTEGER CHECK (nBits >= 0 AND nBits < 0x100000000),
    nNonce              INTEGER CHECK (nNonce >= 0 AND nNonce < 0x100000000),
    -- Committed Metadata
    payout_address      BLOB NOT NULL,
    start_timestamp     INTEGER NOT NULL,           -- 64-bit unix epoch in MICROseconds
    comm_pub_key        BLOB NOT NULL,
    min_target          INTEGER CHECK (min_target >= 0 AND min_target < 0x100000000),
    weak_target         INTEGER CHECK (weak_target >= 0 AND weak_target < 0x100000000),
    miner_ip            TEXT NOT NULL,
    -- UnCommitted Metadata
    extranonce1         TEXT NOT NULL,
    extranonce2         TEXT NOT NULL,
    broadcast_timestamp INTEGER NOT NULL,       -- 64-bit unix epoch in MICROseconds
    signature           BLOB NOT NULL,
    -- Constraints
    UNIQUE (nVersion, hashPrevBlock, hashMerkleRoot, nTime, nBits, nNonce),
    UNIQUE (hash)
);

-- 2. Transactions
CREATE TABLE Transactions (
      bead_id           INTEGER NOT NULL REFERENCES Bead(id),
      txid              BLOB,
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
CREATE INDEX bead_hash ON Bead(hash);
CREATE INDEX timestamps_parents ON ParentTimestamps(parent);
CREATE INDEX timestamps_children ON ParentTimestamps(child);
CREATE INDEX bead_start_timestamp ON Bead(start_timestamp);
CREATE INDEX parent_timestamps_timestamp ON ParentTimestamps(timestamp);

-- 8. WAL mode for append-only workloads
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
PRAGMA foreign_keys = ON;
