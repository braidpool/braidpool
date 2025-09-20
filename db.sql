-- 1. CommittedMetadata
CREATE TABLE CommittedMetadata (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    transactions    TEXT NOT NULL CHECK (    
	json_valid(transactions)
	    AND json_type(transactions) = 'array'
	    AND NOT EXISTS (
		SELECT 1
		FROM json_each(transactions)
		WHERE length(value) != 64
		   OR value NOT GLOB '[0-9A-Fa-f][0-9A-Fa-f]*'
	    )
	),          				-- JSON array of TXIDs
    payout_address  TEXT NOT NULL CHECK (length(payout_address) <= 128),
    start_timestamp INTEGER NOT NULL,       	-- unix epoch in MICROseconds
    comm_pub_key    TEXT NOT NULL CHECK (length(comm_pub_key) <= 512),
    min_target      TEXT NOT NULL CHECK (length(min_target) = 8 AND min_target GLOB '[0-9a-f]*'),
    weak_target     TEXT NOT NULL CHECK (length(weak_target) = 8 AND weak_target GLOB '[0-9a-f]*'),
    miner_ip        TEXT NOT NULL CHECK (length(miner_ip) <= 45)
);

-- 2. UnCommittedMetadata
CREATE TABLE UnCommittedMetadata (
    id                  INTEGER PRIMARY KEY AUTOINCREMENT,
    extra_nonce         INTEGER NOT NULL,
    broadcast_timestamp INTEGER NOT NULL,   	-- unix epoch in MICROseconds
    signature           TEXT NOT NULL
);

-- 3. Bead
CREATE TABLE Bead (
    id                      INTEGER PRIMARY KEY AUTOINCREMENT,
    block_header            TEXT NOT NULL UNIQUE,
    committed_metadata_id   INTEGER NOT NULL,
    uncommitted_metadata_id INTEGER NOT NULL,
    FOREIGN KEY (committed_metadata_id)
        REFERENCES CommittedMetadata(id),
    FOREIGN KEY (uncommitted_metadata_id)
        REFERENCES UnCommittedMetadata(id)
);

-- 4. Cohorts
-- Cohorts are a bit complicated because of the desire to be append-only.
-- Work in progress

-- 5. Relatives (parent/child link)
CREATE TABLE Relatives (
    child  INTEGER NOT NULL,
    parent INTEGER NOT NULL,
    PRIMARY KEY (parent, child),
    FOREIGN KEY (child)  REFERENCES Bead(id),
    FOREIGN KEY (parent) REFERENCES Bead(id)
);

-- 6. Individual timestamps: one row per (child, parent)
CREATE TABLE WitnessedTimestamps (
    child  INTEGER NOT NULL,
    parent INTEGER NOT NULL,
    ts     INTEGER NOT NULL,   			-- unix epoch in MICROseconds
    PRIMARY KEY (parent, child),   		-- exactly one timestamp per link
    FOREIGN KEY (child)  REFERENCES Bead(id),
    FOREIGN KEY (parent) REFERENCES Bead(id),
    FOREIGN KEY (parent, child) REFERENCES Relatives(parent, child)
);

-- 7. Fast look-up indices
CREATE INDEX parents ON Relatives(parent);
CREATE INDEX children ON Relatives(child);
CREATE INDEX headers ON Bead(block_header);

-- 8. Indices to look up parent timestamps from the child and v/v
CREATE INDEX ts_parent_child ON WitnessedTimestamps(parent, child);
CREATE INDEX ts_child_parent ON WitnessedTimestamps(child, parent);

-- 9. WAL mode for append-only workloads
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
