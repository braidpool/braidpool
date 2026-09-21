-- Braidpool Audit Mode Database Schema                
PRAGMA foreign_keys = ON;
PRAGMA journal_mode = WAL;

CREATE TABLE IF NOT EXISTS AuditBead (
    id                  INTEGER PRIMARY KEY,
    composite_hash      BLOB NOT NULL UNIQUE,       
    block_hash          BLOB NOT NULL UNIQUE,           
    version             INTEGER NOT NULL CHECK (version >= 0 AND version < 0x100000000),
    prev_block_hash     BLOB NOT NULL,
    merkle_root         BLOB NOT NULL,
    timestamp           INTEGER NOT NULL CHECK (timestamp >= 0 AND timestamp < 0x100000000),
    bits                INTEGER NOT NULL CHECK (bits >= 0 AND bits < 0x100000000),
    nonce               INTEGER NOT NULL CHECK (nonce >= 0 AND nonce < 0x100000000),    
    payout_address      TEXT NOT NULL,
    start_timestamp     INTEGER NOT NULL,
    comm_pub_key        BLOB NOT NULL,
    min_target          INTEGER NOT NULL CHECK (min_target >= 0 AND min_target < 0x100000000),
    weak_target         INTEGER NOT NULL CHECK (weak_target >= 0 AND weak_target < 0x100000000),
    miner_ip            TEXT NOT NULL,    
    extranonce1         TEXT NOT NULL,
    extranonce2         TEXT NOT NULL,
    broadcast_timestamp INTEGER NOT NULL,
    signature           BLOB NOT NULL,    
    created_at          INTEGER NOT NULL,
    UNIQUE (version, prev_block_hash, merkle_root, timestamp, bits, nonce)
);

-- Represents DAG parent relationships
CREATE TABLE IF NOT EXISTS AuditBeadParent (
    child_id            INTEGER NOT NULL,
    parent_block_hash BLOB NOT NULL,            
    parent_timestamp    INTEGER NOT NULL,           
    
    PRIMARY KEY (child_id, parent_block_hash),
    FOREIGN KEY (child_id) REFERENCES AuditBead(id) ON DELETE CASCADE,
    FOREIGN KEY (parent_block_hash) REFERENCES AuditBead(block_hash) ON DELETE RESTRICT
);

-- Indexes
CREATE INDEX IF NOT EXISTS idx_audit_bead_composite ON AuditBead(composite_hash);
CREATE INDEX IF NOT EXISTS idx_audit_bead_block ON AuditBead(block_hash);
CREATE INDEX IF NOT EXISTS idx_audit_bead_miner ON AuditBead(miner_ip);
CREATE INDEX IF NOT EXISTS idx_audit_bead_created ON AuditBead(created_at DESC);

CREATE INDEX IF NOT EXISTS idx_audit_parent_child ON AuditBeadParent(child_id);
CREATE INDEX IF NOT EXISTS idx_audit_parent_hash ON AuditBeadParent(parent_block_hash);

-- Views 
-- Real time health and performance statistics for each connected miner.
CREATE VIEW IF NOT EXISTS MinerStatsView AS
SELECT 
    miner_ip,
    COUNT(*) as total_valid_beads,
    MIN(created_at) as first_bead_at,
    MAX(created_at) as last_bead_at
FROM AuditBead
GROUP BY miner_ip;

-- Audit DAG tips view
CREATE VIEW IF NOT EXISTS AuditTips AS
SELECT ab.*
FROM AuditBead ab
LEFT JOIN AuditBeadParent abp ON abp.parent_block_hash = ab.block_hash
WHERE abp.child_id IS NULL;