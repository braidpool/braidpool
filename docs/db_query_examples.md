# SQLite Query Examples for Braidpool Database

## Basic DAG Navigation

### 1. **All children of the given parent**
   (parent id = :pid)

```sql
SELECT b.*
FROM Bead b
JOIN Relatives r ON r.child = b.id
WHERE r.parent = :pid
ORDER BY b.id;
```

### 2. **All ancestors of a bead (recursive)**
   (child id = :cid)

```sql
WITH RECURSIVE ancestors(id) AS (
    SELECT :cid
    UNION
    SELECT r.parent
    FROM Relatives r
    JOIN ancestors a ON a.id = r.child
)
SELECT * FROM Bead WHERE id IN (SELECT id FROM ancestors);
```

### 3. **All descendants of a bead (recursive)**
   (parent id = :pid)

```sql
WITH RECURSIVE descendants(id) AS (
    SELECT :pid
    UNION
    SELECT r.child
    FROM Relatives r
    JOIN descendants d ON d.id = r.parent
)
SELECT * FROM Bead WHERE id IN (SELECT id FROM descendants);
```


### 4. **Beads that have no parents (genesis beads)**

```sql
SELECT b.*
FROM Bead b
LEFT JOIN Relatives r ON r.child = b.id
WHERE r.child IS NULL;
```

### 5. **Beads that have no children (leaf beads)**

```sql
SELECT b.*
FROM Bead b
LEFT JOIN Relatives r ON r.parent = b.id
WHERE r.parent IS NULL;
```

## Time-Based Queries

### 6. **Beads created within time range**
   (start_time = :start, end_time = :end)

```sql
SELECT *
FROM Bead
WHERE start_timestamp BETWEEN :start AND :end
ORDER BY start_timestamp;
```

### 7. **Beads broadcast within time range**
   (start_time = :start, end_time = :end)

```sql
SELECT *
FROM Bead
WHERE broadcast_timestamp BETWEEN :start AND :end
ORDER BY broadcast_timestamp;
```

### 8. **Parent-witness timestamps within time range**
   (start_time = :start, end_time = :end)

```sql
SELECT pt.*, b_child.hash as child_hash, b_parent.hash as parent_hash
FROM ParentTimestamps pt
JOIN Bead b_child ON b_child.id = pt.child
JOIN Bead b_parent ON b_parent.id = pt.parent
WHERE pt.timestamp BETWEEN :start AND :end
ORDER BY pt.timestamp;
```

### 9. **Average time between parent and child witnessing**
    (micro-seconds)

```sql
SELECT AVG(c.broadcast_timestamp - p.broadcast_timestamp) AS avg_microseconds
FROM Relatives r
JOIN Bead child ON child.id = r.child
JOIN Bead parent ON parent.id = r.parent
WHERE r.child = :cid;
```

### 10. **Average witnessing delay**
    (time from bead creation to witnessing parents)

```sql
SELECT AVG(pt.timestamp - parent.start_timestamp) AS avg_witnessing_delay
FROM ParentTimestamps pt
JOIN Bead parent ON parent.id = pt.parent
WHERE pt.parent = :pid;
```

## Transaction Queries

### 11. **Beads containing a specific TXID**
    (txid = :txid)

```sql
SELECT b.*
FROM Bead b
JOIN Transactions t ON t.bead_id = b.id
WHERE t.txid = :txid;
```

### 12. **All TXIDs for a specific bead**
    (bead_id = :bid)

```sql
SELECT txid
FROM Transactions
WHERE bead_id = :bid
ORDER BY txid;
```

## Timestamp Analysis

### 13. **Latest bead (highest broadcast timestamp)**

```sql
SELECT *
FROM Bead
ORDER BY broadcast_timestamp DESC
LIMIT 1;
```

### 14. **Beads with oldest parent timestamps**

```sql
SELECT b.*, pt.timestamp as parent_witness_time
FROM Bead b
JOIN ParentTimestamps pt ON pt.child = b.id
ORDER BY pt.timestamp ASC
LIMIT 10;
```

## Mining and Target Analysis

### 15. **Beads with specific difficulty range**
    (min_target = :min_target, max_target = :max_target)

```sql
SELECT *
FROM Bead
WHERE min_target BETWEEN :min_target AND :max_target
ORDER BY min_target;
```

### 16. **Average mining time**
    (time from start to broadcast)

```sql
SELECT AVG(broadcast_timestamp - start_timestamp) AS avg_mining_time
FROM Bead
WHERE broadcast_timestamp > start_timestamp;
```

### 17. **Top miners by bead count**

```sql
SELECT miner_ip, COUNT(*) AS bead_count
FROM Bead
GROUP BY miner_ip
ORDER BY bead_count DESC
LIMIT 10;
```

## Cohort Management

### 18. **Add or move a bead into the latest cohort**
    (assumes at least one cohort exists)

```sql
INSERT INTO Cohorts (bead_id, cohort_id)
VALUES (:bead_id, (SELECT MAX(id) FROM CohortIds))
ON CONFLICT(bead_id) DO UPDATE SET cohort_id = excluded.cohort_id;
```

### 19. **Assign a batch of beads to a specific cohort**
    (cohort_id = :cohort_id)

```sql
WITH bead_batch(bead_id) AS (
    VALUES (201), (202), (203)
)
INSERT INTO Cohorts (bead_id, cohort_id)
SELECT bead_id, :cohort_id
FROM bead_batch
ON CONFLICT(bead_id) DO UPDATE SET cohort_id = excluded.cohort_id;
```

### 20. **List beads belonging to a cohort**
    (cohort_id = :cohort_id)

```sql
SELECT b.*
FROM Bead b
JOIN Cohorts c ON c.bead_id = b.id
WHERE c.cohort_id = :cohort_id
ORDER BY b.id;
```

## Complex Multi-Table Queries

### 21. **Full bead details with all parents and transactions**

```sql
SELECT b.*,
       GROUP_CONCAT(DISTINCT p.hash) as parent_hashes,
       GROUP_CONCAT(DISTINCT t.txid) as txids
FROM Bead b
LEFT JOIN Relatives r ON r.child = b.id
LEFT JOIN Bead p ON p.id = r.parent
LEFT JOIN Transactions t ON t.bead_id = b.id
WHERE b.id = :bid
GROUP BY b.id;
```

### 22. **Find all ancestors of a specific bead**
    (tip_id = :tip_id)

```sql
WITH RECURSIVE ancestors(id) AS (
    SELECT :tip_id
    UNION
    SELECT r.parent
    FROM Relatives r
    JOIN ancestors a ON a.id = r.child
)
SELECT b.* FROM Bead b
JOIN ancestors a ON b.id = a.id
ORDER BY b.start_timestamp;
```

### 23. **Detect potential orphan branches**
    (beads that haven't been witnessed recently)

```sql
SELECT b.*
FROM Bead b
LEFT JOIN ParentTimestamps pt ON pt.parent = b.id
WHERE b.broadcast_timestamp < :cutoff_time
  AND pt.parent IS NULL
  AND EXISTS (SELECT 1 FROM Relatives r WHERE r.parent = b.id);
```

### 24. **Insert a bead and all dependent rows atomically**

Uses JSON arrays to handle variable numbers of transactions, relatives, and timestamps. Requires SQLite 3.38+.

```sql
BEGIN TRANSACTION;

    INSERT INTO bead (
        id, hash, nVersion, hashPrevBlock, hashMerkleRoot, nTime,
        nBits, nNonce, payout_address, start_timestamp, comm_pub_key,
        min_target, weak_target, miner_ip, extra_nonce,
        broadcast_timestamp, signature
    )
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);

    INSERT INTO Transactions (bead_id, txid)
    SELECT 
        json_extract(value, '$.bead_id') AS bead_id,
        json_extract(value, '$.txid') AS txid
    FROM json_each(?);

    INSERT INTO Relatives (child, parent) 
    SELECT json_extract(value,'$.child') AS child,
        json_extract(value,'$.parent') AS PARENT
    FROM json_each(?);

    INSERT INTO ParentTimestamps (parent, child, timestamp)
    SELECT json_extract(value,'$.parent') AS parent,
            json_extract(value,'$.child') AS child,
            json_extract(value,'$.timestamp') AS timestamp
    FROM json_each(?);
    COMMIT;
```

**Parameters:**
- `:transactions_json` = `'["txid1","txid2","txid3"]'` (or empty array `'[]'`)
- `:relatives_json` = `'[1,2]'`
- `:parent_timestamps_json` = `'[{"parent":1,"timestamp":1234567890},{"parent":2,"timestamp":1234567891}]'`

This approach uses `json_each()` to iterate over JSON arrays, allowing variable numbers of dependent rows without string generation. All operations are atomic within a single transaction.
