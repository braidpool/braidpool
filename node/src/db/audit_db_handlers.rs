use crate::bead::Bead;
use crate::error::DBErrors;
use bitcoin::BlockHash;
use sqlx::{Pool, Sqlite};
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

const INSERT_BEAD_QUERY: &str = "
INSERT INTO AuditBead (
    composite_hash, block_hash,
    version, prev_block_hash, merkle_root, timestamp, bits, nonce,
    payout_address, start_timestamp, comm_pub_key, min_target, weak_target, miner_ip,
    extranonce1, extranonce2, broadcast_timestamp, signature,
    created_at
) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
";

pub struct AuditDBHandler {
    db_connection_pool: Pool<Sqlite>,
}

impl AuditDBHandler {
    pub async fn new() -> Result<Self, DBErrors> {
        let connection = match crate::db::init_db::init_audit_db().await {
            Ok(conn) => conn,
            Err(error) => {
                error!(error = ?error, "Failed to initialize audit database connection");
                return Err(error);
            }
        };

        Ok(Self {
            db_connection_pool: connection,
        })
    }

    pub async fn insert_bead(
        &self,
        bead: &Bead,
        composite_hash: BlockHash,
        miner_ip: String,
    ) -> Result<i64, DBErrors> {
        let mut tx = match self.db_connection_pool.begin().await {
            Ok(tx) => tx,
            Err(e) => {
                return Err(DBErrors::ConnectionToSQlitePoolFailed {
                    error: e.to_string(),
                })
            }
        };

        let block_hash = bead.block_header.block_hash();
        let created_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64;

        let extranonce1 = format!("{:016x}", bead.uncommitted_metadata.extra_nonce_1);
        let extranonce2 = format!("{:016x}", bead.uncommitted_metadata.extra_nonce_2);

        let result = sqlx::query(INSERT_BEAD_QUERY)
            .bind(composite_hash.as_byte_array().as_slice())
            .bind(block_hash.as_byte_array().as_slice())
            .bind(bead.block_header.version.to_consensus() as i64)
            .bind(bead.block_header.prev_blockhash.as_byte_array().as_slice())
            .bind(bead.block_header.merkle_root.as_byte_array().as_slice())
            .bind(bead.block_header.time.to_u32() as i64)
            .bind(bead.block_header.bits.to_consensus() as i64)
            .bind(bead.block_header.nonce as i64)
            .bind(&bead.committed_metadata.payout_address)
            .bind(bead.committed_metadata.start_timestamp.to_u32() as i64)
            .bind(bead.committed_metadata.comm_pub_key.to_bytes())
            .bind(bead.committed_metadata.min_target.to_consensus() as i64)
            .bind(bead.committed_metadata.weak_target.to_consensus() as i64)
            .bind(miner_ip)
            .bind(extranonce1)
            .bind(extranonce2)
            .bind(bead.uncommitted_metadata.broadcast_timestamp.to_u32() as i64)
            .bind(bead.uncommitted_metadata.signature.to_vec())
            .bind(created_at)
            .execute(&mut *tx)
            .await
            .map_err(|e| DBErrors::TupleNotInserted {
                error: e.to_string(),
            })?;

        let bead_id = result.last_insert_rowid();

        let parents: Vec<_> = bead
            .committed_metadata
            .parents
            .iter()
            .zip(bead.committed_metadata.parent_bead_timestamps.0.iter())
            .collect();

        if !parents.is_empty() {
            let mut qb = sqlx::QueryBuilder::new(
                "INSERT INTO AuditBeadParent (child_id, parent_block_hash, parent_timestamp) ",
            );
            qb.push_values(parents, |mut b, (parent_hash, parent_timestamp)| {
                b.push_bind(bead_id)
                    .push_bind(parent_hash.as_byte_array().as_slice())
                    .push_bind(parent_timestamp.to_u32() as i64);
            });
            qb.build()
                .execute(&mut *tx)
                .await
                .map_err(|e| DBErrors::TupleNotInserted {
                    error: e.to_string(),
                })?;
        }

        tx.commit()
            .await
            .map_err(|e| DBErrors::InsertionTransactionNotCommitted {
                error: e.to_string(),
                query_name: "Audit Bead Insertion".to_string(),
            })?;

        Ok(bead_id)
    }

    /// Shared helper to reconstruct a Bead from a database row and fetch its parents
    async fn parse_bead_row(
        pool: &sqlx::Pool<sqlx::Sqlite>,
        row: sqlx::sqlite::SqliteRow,
    ) -> Result<(Bead, BlockHash), DBErrors> {
        use sqlx::Row;

        let composite_hash_bytes: Vec<u8> = row.get("composite_hash");
        let composite_hash = match composite_hash_bytes.try_into() {
            Ok(arr) => BlockHash::from_byte_array(arr),
            Err(_) => {
                return Err(DBErrors::TupleAttributeParsingError {
                    error: "Invalid composite hash bytes".to_string(),
                    attribute: "composite_hash".to_string(),
                })
            }
        };

        let version = bitcoin::block::Version::from_consensus(row.get::<i64, _>("version") as i32);
        let prev_hash_bytes: Vec<u8> = row.get("prev_block_hash");
        let prev_blockhash =
            BlockHash::from_byte_array(prev_hash_bytes.try_into().map_err(|_| {
                DBErrors::TupleAttributeParsingError {
                    error: "Expected 32 bytes".to_string(),
                    attribute: "prev_block_hash".to_string(),
                }
            })?);
        let merkle_bytes: Vec<u8> = row.get("merkle_root");
        let merkle_root =
            bitcoin::TxMerkleNode::from_byte_array(merkle_bytes.try_into().map_err(|_| {
                DBErrors::TupleAttributeParsingError {
                    error: "Expected 32 bytes".to_string(),
                    attribute: "merkle_root".to_string(),
                }
            })?);
        let timestamp = bitcoin::BlockTime::from_u32(row.get::<i64, _>("timestamp") as u32);
        let bits = bitcoin::CompactTarget::from_consensus(row.get::<i64, _>("bits") as u32);
        let nonce = row.get::<i64, _>("nonce") as u32;

        let block_header = bitcoin::BlockHeader {
            version,
            prev_blockhash,
            merkle_root,
            time: timestamp,
            bits,
            nonce,
        };

        // Committed metadata
        let payout_address = row.get::<String, _>("payout_address");
        let start_timestamp = bitcoin::absolute::MedianTimePast::from_u32(
            row.get::<i64, _>("start_timestamp") as u32,
        )
        .map_err(|e| DBErrors::TupleAttributeParsingError {
            error: e.to_string(),
            attribute: "start_timestamp".to_string(),
        })?;

        let comm_pub_key_bytes: Vec<u8> = row.get("comm_pub_key");
        let comm_pub_key = bitcoin::PublicKey::from_slice(&comm_pub_key_bytes).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "comm_pub_key".to_string(),
            }
        })?;
        let min_target =
            bitcoin::CompactTarget::from_consensus(row.get::<i64, _>("min_target") as u32);
        let weak_target =
            bitcoin::CompactTarget::from_consensus(row.get::<i64, _>("weak_target") as u32);
        let miner_ip = row.get::<String, _>("miner_ip");

        // Uncommitted metadata
        let extranonce1 =
            u64::from_str_radix(&row.get::<String, _>("extranonce1"), 16).map_err(|e| {
                DBErrors::TupleAttributeParsingError {
                    error: e.to_string(),
                    attribute: "extranonce1".to_string(),
                }
            })?;
        let extranonce2 =
            u64::from_str_radix(&row.get::<String, _>("extranonce2"), 16).map_err(|e| {
                DBErrors::TupleAttributeParsingError {
                    error: e.to_string(),
                    attribute: "extranonce2".to_string(),
                }
            })?;
        let broadcast_timestamp = bitcoin::absolute::MedianTimePast::from_u32(
            row.get::<i64, _>("broadcast_timestamp") as u32,
        )
        .map_err(|e| DBErrors::TupleAttributeParsingError {
            error: e.to_string(),
            attribute: "broadcast_timestamp".to_string(),
        })?;
        let signature_bytes: Vec<u8> = row.get("signature");
        let signature = bitcoin::ecdsa::Signature::from_slice(&signature_bytes).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "signature".to_string(),
            }
        })?;
        // Fetch parents for this specific bead
        let bead_id: i64 = row.get("id");
        let parent_rows = sqlx::query(
            "SELECT parent_block_hash, parent_timestamp FROM AuditBeadParent WHERE child_id = ?",
        )
        .bind(bead_id)
        .fetch_all(pool)
        .await
        .map_err(|e| DBErrors::TupleNotFetched {
            error: format!("Failed to fetch parents for bead id {}: {}", bead_id, e),
        })?;

        let mut parent_pairs: Vec<(BlockHash, bitcoin::absolute::Time)> = Vec::new();

        for p_row in parent_rows {
            let p_hash: Vec<u8> = p_row.get("parent_block_hash");
            let hash = BlockHash::from_byte_array(p_hash.try_into().map_err(|_| {
                DBErrors::TupleAttributeParsingError {
                    error: "Expected 32 bytes".to_string(),
                    attribute: "parent_block_hash".to_string(),
                }
            })?);
            let time = bitcoin::absolute::MedianTimePast::from_u32(
                p_row.get::<i64, _>("parent_timestamp") as u32,
            )
            .map_err(|e| DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "parent_timestamp".to_string(),
            })?;
            parent_pairs.push((hash, time));
        }
        parent_pairs.sort_by_key(|(hash, _)| *hash);
        let mut parents: Vec<BlockHash> = Vec::new();
        let mut parent_timestamps = Vec::new();
        for (hash, time) in parent_pairs {
            parents.push(hash);
            parent_timestamps.push(time);
        }

        let bead = Bead {
            block_header,
            committed_metadata: crate::committed_metadata::CommittedMetadata {
                transaction_ids: crate::TxIdVec(Vec::new()),
                parents,
                parent_bead_timestamps: crate::TimeVec(parent_timestamps),
                payout_address,
                start_timestamp,
                comm_pub_key,
                min_target,
                weak_target,
                miner_ip,
            },
            uncommitted_metadata: crate::uncommitted_metadata::UnCommittedMetadata {
                extra_nonce_1: extranonce1,
                extra_nonce_2: extranonce2,
                broadcast_timestamp,
                signature,
            },
        };

        Ok((bead, composite_hash))
    }

    // Used to return the current active tips in audit braid
    pub async fn get_tips(&self) -> Result<Vec<(Bead, BlockHash)>, DBErrors> {
        let pool = &self.db_connection_pool;

        let rows = sqlx::query(
            r#"
            SELECT * FROM AuditBead 
            WHERE block_hash NOT IN (
                SELECT parent_block_hash FROM AuditBeadParent
            )
            "#,
        )
        .fetch_all(pool)
        .await
        .map_err(|e| DBErrors::TupleNotFetched {
            error: format!("Failed to fetch DAG tips: {}", e),
        })?;

        let mut tips = Vec::new();
        for row in rows {
            let parsed = Self::parse_bead_row(pool, row).await?;
            tips.push(parsed);
        }

        Ok(tips)
    }

    pub async fn get_bead_by_composite_hash(
        &self,
        composite_hash: &BlockHash,
    ) -> Result<Option<i64>, DBErrors> {
        let pool = &self.db_connection_pool;
        let result =
            sqlx::query_scalar::<_, i64>("SELECT id FROM AuditBead WHERE composite_hash = ?")
                .bind(composite_hash.as_byte_array().as_slice())
                .fetch_optional(pool)
                .await
                .map_err(|e| DBErrors::TupleNotFetched {
                    error: e.to_string(),
                })?;

        Ok(result)
    }

    pub async fn get_miner_stats(&self, miner_ip: &str) -> Result<MinerStats, DBErrors> {
        let pool = &self.db_connection_pool;
        let result =
            sqlx::query_as::<_, MinerStats>("SELECT * FROM MinerStatsView WHERE miner_ip = ?")
                .bind(miner_ip)
                .fetch_optional(pool)
                .await
                .map_err(|e| DBErrors::TupleNotFetched {
                    error: e.to_string(),
                })?;

        Ok(result.unwrap_or_default())
    }

    pub async fn get_bead_count(&self) -> Result<i64, DBErrors> {
        let pool = &self.db_connection_pool;
        let row: (i64,) = sqlx::query_as("SELECT COUNT(*) FROM AuditBead")
            .fetch_one(pool)
            .await
            .map_err(|e| DBErrors::TupleNotFetched {
                error: e.to_string(),
            })?;
        Ok(row.0)
    }
}

#[derive(Debug, Clone, Default)]
pub struct MinerStats {
    pub miner_ip: String,
    pub total_valid_beads: i64,
    pub first_bead_at: Option<i64>,
    pub last_bead_at: Option<i64>,
}

impl sqlx::FromRow<'_, sqlx::sqlite::SqliteRow> for MinerStats {
    fn from_row(row: &sqlx::sqlite::SqliteRow) -> Result<Self, sqlx::Error> {
        use sqlx::Row;
        Ok(Self {
            miner_ip: row.try_get("miner_ip")?,
            total_valid_beads: row.try_get("total_valid_beads")?,
            first_bead_at: row.try_get("first_bead_at")?,
            last_bead_at: row.try_get("last_bead_at")?,
        })
    }
}
