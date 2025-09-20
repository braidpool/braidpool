1. **All children of the given parent**  
   (parent id = :pid)

```sql
SELECT b.*
FROM Bead b
JOIN Relatives r ON r.child = b.id
WHERE r.parent = :pid
ORDER BY b.id;
```

2. **All ancestors of a bead (recursive)**  
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

3. **All descendants of a bead (recursive)**  
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

4. **Longest chain length (height) from a bead**  
   (parent id = :pid)

```sql
WITH RECURSIVE height(id, lvl) AS (
    SELECT :pid, 0
    UNION ALL
    SELECT r.child, h.lvl + 1
    FROM Relatives r
    JOIN height h ON h.id = r.parent
)
SELECT MAX(lvl) AS max_height FROM height;
```

5. **Beads that have no parents (genesis beads)**

```sql
SELECT b.*
FROM Bead b
LEFT JOIN Relatives r ON r.child = b.id
WHERE r.child IS NULL;
```

6. **Beads that have no children (leaf beads)**

```sql
SELECT b.*
FROM Bead b
LEFT JOIN Relatives r ON r.parent = b.id
WHERE r.parent IS NULL;
```

7. **Average time between parent and child**  
   (micro-seconds)

```sql
SELECT AVG(c_um.broadcast_timestamp - p_um.broadcast_timestamp) AS avg_microseconds
FROM Relatives r
JOIN Bead child   ON child.id   = r.child
JOIN Bead parent  ON parent.id  = r.parent
JOIN UnCommittedMetadata c_um ON c_um.id  = child.uncommitted_metadata_id
JOIN UnCommittedMetadata p_um ON p_um.id = parent.uncommitted_metadata_id
WHERE r.child = :cid;
```

8. **Top-10 parents with the most children**

```sql
SELECT parent, COUNT(*) AS child_cnt
FROM Relatives
GROUP BY parent
ORDER BY child_cnt DESC
LIMIT 10;
```

9. **Top-10 children with the most parents (merge points)**

```sql
SELECT child, COUNT(*) AS parent_cnt
FROM Relatives
GROUP BY child
ORDER BY parent_cnt DESC
LIMIT 10;
```

10. **Distribution of chain lengths (histogram)**

```sql
WITH RECURSIVE chain_len(id, len) AS (
    SELECT parent, 0 FROM Relatives
    UNION ALL
    SELECT r.child, c.len + 1
    FROM Relatives r
    JOIN chain_len c ON c.id = r.parent
)
SELECT len, COUNT(*) AS cnt
FROM chain_len
GROUP BY len
ORDER BY len;
```

11. **Beads whose committed metadata contains a specific TXID**  
   (txid = :txid)

```sql
SELECT b.*
FROM Bead b
JOIN CommittedMetadata cm ON cm.id = b.committed_metadata_id
WHERE EXISTS (
    SELECT 1
    FROM json_each(cm.transactions)
    WHERE value = :txid
);
```

12. **Latest bead (highest broadcast timestamp)**

```sql
SELECT b.*
FROM Bead b
JOIN UnCommittedMetadata um ON um.id = b.uncommitted_metadata_id
ORDER BY um.broadcast_timestamp DESC
LIMIT 1;
```

