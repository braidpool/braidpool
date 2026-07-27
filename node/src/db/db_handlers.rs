use crate::{
    bead::Bead,
    db::{init_db::init_db, BeadInsertData, BraidpoolDBTypes, InsertTupleTypes},
    error::DBErrors,
};
use bitcoin::{
    absolute::MedianTimePast, ecdsa::Signature, BlockHash, BlockTime, BlockVersion, CompactTarget,
    PublicKey, TxMerkleNode, Txid,
};
use serde_json::json;
use sqlx::{Pool, Row, Sqlite};
use tokio::sync::mpsc::{Receiver, Sender};
#[cfg(test)]
use tracing::info;
use tracing::{debug, error, trace};
pub const DB_CHANNEL_CAPACITY: usize = 1024;
/// Maximum number of beads (including orphans) to insert in a single bulk query to limit the memory consumption
pub const BATCH_INSERT_THRESHOLD: usize = 500;
pub const FETCH_BEAD_BATCH_SIZE: u32 = 50;
//Bulk insertion sub-queries
const BULK_INSERT_BEADS: &str =
    "INSERT INTO bead (id, hash, nVersion, hashPrevBlock, hashMerkleRoot, nTime, 
        nBits, nNonce, payout_address, start_timestamp, comm_pub_key, min_target, 
        weak_target, miner_ip, extranonce1, extranonce2, broadcast_timestamp, signature) 
    SELECT 
        json_extract(value, '$.id'), 
        unhex(json_extract(value, '$.hash')), 
        json_extract(value, '$.nVersion'), 
        unhex(json_extract(value, '$.hashPrevBlock')), 
        unhex(json_extract(value, '$.hashMerkleRoot')), 
        json_extract(value, '$.nTime'), 
        json_extract(value, '$.nBits'), 
        json_extract(value, '$.nNonce'),
        unhex(json_extract(value, '$.payout_address')),
        json_extract(value, '$.start_timestamp'),
        unhex(json_extract(value, '$.comm_pub_key')), 
        json_extract(value, '$.min_target'), 
        json_extract(value, '$.weak_target'), 
        json_extract(value, '$.miner_ip'), 
        json_extract(value, '$.extranonce1'), 
        json_extract(value, '$.extranonce2'), 
        json_extract(value, '$.broadcast_timestamp'), 
        unhex(json_extract(value, '$.signature')) 
    FROM json_each(?);";
//Separating into sub-queries
const BULK_INSERT_TRANSACTIONS: &str = "INSERT INTO Transactions (bead_id, txid) 
    SELECT json_extract(value, '$.bead_id'), unhex(json_extract(value, '$.txid')) 
    FROM json_each(?);";

const BULK_INSERT_RELATIVES: &str = "INSERT INTO Relatives (child, parent) 
    SELECT json_extract(value, '$.child'), json_extract(value, '$.parent') 
    FROM json_each(?);";

const BULK_INSERT_PARENT_TIMESTAMPS: &str =
    "INSERT INTO ParentTimestamps (parent, child, timestamp) 
    SELECT json_extract(value, '$.parent'), json_extract(value, '$.child'), 
        json_extract(value, '$.timestamp') 
    FROM json_each(?);";
#[derive(Debug)]
pub struct DBHandler {
    //Query receiver inherit to handler only
    receiver: Receiver<BraidpoolDBTypes>,
    //Shared across tasks for accessing DB after contention using `Mutex`
    pub db_connection_pool: Pool<Sqlite>,
}
impl DBHandler {
    pub async fn new() -> Result<(Self, Sender<BraidpoolDBTypes>), DBErrors> {
        debug!("Initializing schema for persistent database");
        let db_connection_pool = match init_db().await {
            Ok(conn) => conn,
            Err(error) => {
                error!(error = ?error, "Failed to initialize database connection");
                return Err(DBErrors::ConnectionToDBNotEstablished {
                    error: error.to_string(),
                });
            }
        };
        let (db_handler_tx, db_handler_rx) = tokio::sync::mpsc::channel(DB_CHANNEL_CAPACITY);
        Ok((
            Self {
                receiver: db_handler_rx,
                db_connection_pool,
            },
            db_handler_tx,
        ))
    }
    /// Builds the `(transactions, relatives, parent_timestamps)` JSON value tuples for a single
    /// bead.
    fn prepare_bead_tuple_values(
        data: &BeadInsertData,
    ) -> (
        Vec<serde_json::Value>,
        Vec<serde_json::Value>,
        Vec<serde_json::Value>,
    ) {
        let bead_id = data.bead_id as u64;
        let mut relatives_values = Vec::with_capacity(data.parent_refs.len());
        let mut parent_ts_values = Vec::with_capacity(data.parent_refs.len());
        for (parent_id, parent_timestamp) in &data.parent_refs {
            relatives_values.push(json!({ "parent": *parent_id, "child": bead_id }));
            parent_ts_values.push(json!({
                "child": bead_id,
                "parent": *parent_id,
                "timestamp": *parent_timestamp,
            }));
            debug!("Parent found with id - {:?}", parent_id);
        }
        let mut txs_values =
            Vec::with_capacity(data.bead.committed_metadata.transaction_ids.0.len());
        for tx in &data.bead.committed_metadata.transaction_ids.0 {
            txs_values.push(json!({
                "txid": hex::encode(tx.to_byte_array()),
                "bead_id": bead_id,
            }));
        }
        (txs_values, relatives_values, parent_ts_values)
    }

    /// Inserting chunks for bulk insertions
    async fn bulk_insert_chunk(
        local_transaction: &mut sqlx::Transaction<'_, sqlx::Sqlite>,
        chunk: &[BeadInsertData],
    ) -> Result<(), DBErrors> {
        let mut all_bead_data = Vec::with_capacity(chunk.len());
        let mut all_txs_json_parts = Vec::new();
        let mut all_relatives_json_parts = Vec::new();
        let mut all_parent_ts_json_parts = Vec::new();

        for data in chunk {
            // For each chunk constructing the query placeholders
            let bead = &data.bead;
            let bead_id = data.bead_id;

            let (txs, relatives, parent_ts) = Self::prepare_bead_tuple_values(data);

            all_bead_data.push(json!({
                "id": bead_id as i64,
                "hash": hex::encode(bead.block_header.block_hash().to_byte_array()),
                "nVersion": bead.block_header.version.to_consensus(),
                "hashPrevBlock": hex::encode(bead.block_header.prev_blockhash.to_byte_array()),
                "hashMerkleRoot": hex::encode(bead.block_header.merkle_root.to_byte_array()),
                "nTime": bead.block_header.time.to_u32(),
                "nBits": bead.block_header.bits.to_consensus(),
                "nNonce": bead.block_header.nonce,
                "payout_address": hex::encode(bead.committed_metadata.payout_address.as_bytes()),
                "start_timestamp": bead.committed_metadata.start_timestamp.to_u32(),
                "comm_pub_key": hex::encode(bead.committed_metadata.comm_pub_key.to_bytes()),
                "min_target": bead.committed_metadata.min_target.to_consensus(),
                "weak_target": bead.committed_metadata.weak_target.to_consensus(),
                "miner_ip": bead.committed_metadata.miner_ip.clone(),
                "extranonce1": hex::encode(bead.uncommitted_metadata.extra_nonce_1.to_be_bytes()),
                "extranonce2": hex::encode(bead.uncommitted_metadata.extra_nonce_2.to_be_bytes()),
                "broadcast_timestamp": bead.uncommitted_metadata.broadcast_timestamp.to_u32(),
                "signature": hex::encode(bead.uncommitted_metadata.signature.to_vec()),
            }));
            all_txs_json_parts.extend(txs);
            all_relatives_json_parts.extend(relatives);
            all_parent_ts_json_parts.extend(parent_ts);
        }

        let beads_json = serde_json::to_string(&all_bead_data).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "bulk_beads".to_string(),
            }
        })?;
        let txs_json = serde_json::to_string(&all_txs_json_parts).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "bulk_transactions".to_string(),
            }
        })?;
        let relatives_json = serde_json::to_string(&all_relatives_json_parts).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "bulk_relatives".to_string(),
            }
        })?;
        let parent_ts_json = serde_json::to_string(&all_parent_ts_json_parts).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "bulk_parent_timestamps".to_string(),
            }
        })?;

        // Execute each bulk insert separately within the same transaction
        sqlx::query(BULK_INSERT_BEADS)
            .bind(&beads_json)
            .execute(&mut **local_transaction)
            .await
            .map_err(|e| {
                error!(error = ?e, "Bulk insert beads failed");
                DBErrors::InsertionTransactionNotCommitted {
                    error: e.to_string(),
                    query_name: "Bulk insert beads".to_string(),
                }
            })?;

        sqlx::query(BULK_INSERT_TRANSACTIONS)
            .bind(&txs_json)
            .execute(&mut **local_transaction)
            .await
            .map_err(|e| {
                error!(error = ?e, "Bulk insert transactions failed");
                DBErrors::InsertionTransactionNotCommitted {
                    error: e.to_string(),
                    query_name: "Bulk insert transactions".to_string(),
                }
            })?;

        sqlx::query(BULK_INSERT_RELATIVES)
            .bind(&relatives_json)
            .execute(&mut **local_transaction)
            .await
            .map_err(|e| {
                error!(error = ?e, "Bulk insert relatives failed");
                DBErrors::InsertionTransactionNotCommitted {
                    error: e.to_string(),
                    query_name: "Bulk insert relatives".to_string(),
                }
            })?;

        sqlx::query(BULK_INSERT_PARENT_TIMESTAMPS)
            .bind(&parent_ts_json)
            .execute(&mut **local_transaction)
            .await
            .map_err(|e| {
                error!(error = ?e, "Bulk insert parent timestamps failed");
                DBErrors::InsertionTransactionNotCommitted {
                    error: e.to_string(),
                    query_name: "Bulk insert parent timestamps".to_string(),
                }
            })?;

        Ok(())
    }

    /// Inserts a batch of beads, batches that are larger than BATCH_INSERT_THRESHOLD are split into bulk chunks of that size .
    async fn insert_beads_batch(
        &self,
        beads: Vec<BeadInsertData>,
        orphans: Vec<BeadInsertData>,
    ) -> Result<(), DBErrors> {
        let total_count = beads.len() + orphans.len();
        // Dividing into number of chunks
        let chunk_count = total_count.div_ceil(BATCH_INSERT_THRESHOLD).max(1);

        debug!(
            bead_count = beads.len(),
            orphan_count = orphans.len(),
            total = total_count,
            chunk_size = BATCH_INSERT_THRESHOLD,
            chunk_count = chunk_count,
            "Batch insertion query received"
        );

        let mut local_transaction = match self.db_connection_pool.begin().await {
            Ok(local_transaction) => local_transaction,
            Err(err) => {
                error!("Failed to begin DB batch transaction: {}", err);
                return Err(DBErrors::ConnectionToSQlitePoolFailed {
                    error: err.to_string(),
                });
            }
        };

        let all_beads: Vec<BeadInsertData> = beads.into_iter().chain(orphans).collect();
        let mut inserted_count = 0u32;
        // Iterating through each chunk and inserting the corrsponding chunk
        for chunk in all_beads.chunks(BATCH_INSERT_THRESHOLD) {
            if let Err(e) = Self::bulk_insert_chunk(&mut local_transaction, chunk).await {
                error!(
                    error = ?e,
                    chunk_size = chunk.len(),
                    inserted_count = inserted_count,
                    "Bulk insert chunk failed, rolling back"
                );
                if let Err(rollback_err) = local_transaction.rollback().await {
                    error!(
                        error = ?rollback_err,
                        "Failed to roll back batch transaction after chunk insert failure"
                    );
                }
                return Err(e);
            }
            inserted_count += chunk.len() as u32;
        }

        match local_transaction.commit().await {
            Ok(_) => {
                debug!(
                    bead_count = inserted_count,
                    chunk_count = chunk_count,
                    "Batch transaction committed successfully"
                );
            }
            Err(error) => {
                error!(error = ?error, "Failed to commit batch transaction");
                return Err(DBErrors::InsertionTransactionNotCommitted {
                    error: error.to_string(),
                    query_name: "Batch insert transaction".to_string(),
                });
            }
        };

        Ok(())
    }
    //Individual insertion operations
    pub async fn insert_query_handler(&mut self) {
        debug!("Query handler task started");
        while let Some(query_request) = self.receiver.recv().await {
            match query_request {
                BraidpoolDBTypes::InsertTupleTypes {
                    query:
                        InsertTupleTypes::InsertBeadsBatch {
                            beads,
                            removed_orphans,
                        },
                } => {
                    debug!(
                        bead_count = beads.len(),
                        orphan_count = removed_orphans.len(),
                        "Received batch insert request"
                    );
                    match self.insert_beads_batch(beads, removed_orphans).await {
                        Ok(_) => {
                            debug!("Batch insertion completed successfully");
                        }
                        Err(error) => {
                            error!(
                                error = ?error,
                                "Failed to insert beads in batch"
                            );
                        }
                    }
                }
            }
        }
    }
}
//Fetching beads in batch
pub async fn fetch_beads_in_batch(
    db_pool: &Pool<Sqlite>,
    batch_size: u32,
) -> Result<Vec<Bead>, DBErrors> {
    // Fetching total number of beads
    let total_rows: i64 = sqlx::query("SELECT COUNT(*) AS row_cnt FROM Bead")
        .fetch_one(db_pool)
        .await
        .map_err(|e| DBErrors::TupleNotFetched {
            error: e.to_string(),
        })?
        .get("row_cnt");

    debug!(
        total_beads = total_rows,
        "Number of beads present locally in persistent DB"
    );
    if total_rows == 0 {
        return Ok(vec![]);
    }

    let batch_size = batch_size.max(1) as i64;
    let mut all_beads: Vec<Bead> = Vec::new();
    // Bead ids are 0-indexed, so the cursor starts below the smallest possible.
    let mut last_id: i64 = -1;

    loop {
        let bead_rows = sqlx::query(
            "SELECT
                b.nVersion            AS nVersion,
                b.nBits               AS nBits,
                b.nTime               AS nTime,
                b.nNonce              AS nNonce,
                b.hashPrevBlock       AS hashPrevBlock,
                b.hashMerkleRoot      AS hashMerkleRoot,
                b.payout_address      AS payout_address,
                b.comm_pub_key        AS comm_pub_key,
                b.min_target          AS min_target,
                b.weak_target         AS weak_target,
                b.miner_ip            AS miner_ip,
                b.start_timestamp     AS start_timestamp,
                b.broadcast_timestamp AS broadcast_timestamp,
                b.extranonce1         AS extranonce1,
                b.extranonce2         AS extranonce2,
                b.signature           AS signature,
                b.id                  AS bead_id
            FROM Bead b
            WHERE b.id > ?
            ORDER BY b.id
            LIMIT ?",
        )
        .bind(last_id)
        .bind(batch_size)
        .fetch_all(db_pool)
        .await
        .map_err(|e| DBErrors::TupleNotFetched {
            error: e.to_string(),
        })?;

        if bead_rows.is_empty() {
            break;
        }

        let mut batch: Vec<Bead> = Vec::with_capacity(bead_rows.len());
        let mut ids: Vec<i64> = Vec::with_capacity(bead_rows.len());

        for row in &bead_rows {
            let bead_id: i64 = row.get("bead_id");
            let bead = build_bead_from_row(row)?;
            batch.push(bead);
            ids.push(bead_id);
            last_id = last_id.max(bead_id);
        }

        let placeholders = ids.iter().map(|_| "?").collect::<Vec<_>>().join(",");

        // Transactions for every bead in the batch.
        let tx_sql =
            format!("SELECT bead_id, txid FROM Transactions WHERE bead_id IN ({placeholders})");
        let mut tx_query = sqlx::query(&tx_sql);
        for id in &ids {
            tx_query = tx_query.bind(id);
        }
        let tx_rows = tx_query
            .fetch_all(db_pool)
            .await
            .map_err(|e| DBErrors::TupleNotFetched {
                error: e.to_string(),
            })?;
        for row in tx_rows {
            let bead_id: i64 = row.get("bead_id");
            let idx = ids
                .binary_search(&bead_id)
                .map_err(|_| DBErrors::TupleNotFetched {
                    error: format!("Transaction references unknown bead_id {bead_id}"),
                })?;
            let tx_bytes: Vec<u8> = row.get("txid");
            let arr: [u8; 32] =
                tx_bytes
                    .try_into()
                    .map_err(|_| DBErrors::TupleAttributeParsingError {
                        error: "Invalid txid length".into(),
                        attribute: "txid".into(),
                    })?;
            batch[idx]
                .committed_metadata
                .transaction_ids
                .0
                .push(Txid::from_byte_array(arr));
        }

        let pt_sql = format!(
            "SELECT pt.child AS child, pt.timestamp AS timestamp, pb.hash AS parent_hash
             FROM ParentTimestamps pt
             JOIN Bead pb ON pb.id = pt.parent
             WHERE pt.child IN ({placeholders})
             ORDER BY pt.child, pt.parent"
        );
        let mut pt_query = sqlx::query(&pt_sql);
        for id in &ids {
            pt_query = pt_query.bind(id);
        }
        let pt_rows = pt_query
            .fetch_all(db_pool)
            .await
            .map_err(|e| DBErrors::TupleNotFetched {
                error: e.to_string(),
            })?;
        for row in pt_rows {
            let child_id: i64 = row.get("child");
            let idx = ids
                .binary_search(&child_id)
                .map_err(|_| DBErrors::TupleNotFetched {
                    error: format!("ParentTimestamp references unknown child bead_id {child_id}"),
                })?;
            let parent_hash: Vec<u8> = row.get("parent_hash");
            let arr: [u8; 32] =
                parent_hash
                    .try_into()
                    .map_err(|_| DBErrors::TupleAttributeParsingError {
                        error: "Invalid parent hash length".into(),
                        attribute: "parent_hash".into(),
                    })?;
            let ts: i64 = row.get("timestamp");
            let parent_ts = MedianTimePast::from_u32(ts as u32).map_err(|e| {
                DBErrors::TupleAttributeParsingError {
                    error: format!("Invalid parent timestamp value {}: {}", ts, e),
                    attribute: "parent_bead_timestamps".into(),
                }
            })?;
            let bead = &mut batch[idx];
            bead.committed_metadata
                .parents
                .insert(BlockHash::from_byte_array(arr));
            bead.committed_metadata
                .parent_bead_timestamps
                .0
                .push(parent_ts);
        }

        let batch_len = batch.len() as i64;
        all_beads.extend(batch);

        // A short page means that we have reached the end of the table.
        if batch_len < batch_size {
            break;
        }
    }

    Ok(all_beads)
}

/// Reconstructs a [`Bead`] from a single `Bead` table row.
fn build_bead_from_row(row: &sqlx::sqlite::SqliteRow) -> Result<Bead, DBErrors> {
    let mut bead = Bead::default();
    bead.block_header.version = BlockVersion::from_consensus(row.get::<i32, _>("nVersion"));
    bead.block_header.bits = CompactTarget::from_consensus(row.get::<u32, _>("nBits"));
    bead.block_header.time = BlockTime::from_u32(row.get::<u32, _>("nTime"));
    bead.block_header.nonce = row.get::<u32, _>("nNonce");

    let prev_bytes: Vec<u8> = row.get("hashPrevBlock");
    bead.block_header.prev_blockhash =
        BlockHash::from_byte_array(prev_bytes.try_into().map_err(|_| {
            DBErrors::TupleAttributeParsingError {
                error: "Invalid prev block hash length".into(),
                attribute: "hashPrevBlock".into(),
            }
        })?);

    let merkle_bytes: Vec<u8> = row.get("hashMerkleRoot");
    bead.block_header.merkle_root =
        TxMerkleNode::from_byte_array(merkle_bytes.try_into().map_err(|_| {
            DBErrors::TupleAttributeParsingError {
                error: "Invalid merkle root length".into(),
                attribute: "hashMerkleRoot".into(),
            }
        })?);

    bead.committed_metadata.payout_address =
        String::from_utf8(row.get::<Vec<u8>, _>("payout_address")).map_err(|_| {
            DBErrors::TupleAttributeParsingError {
                error: "Invalid payout_address UTF-8".into(),
                attribute: "payout_address".into(),
            }
        })?;

    bead.committed_metadata.comm_pub_key =
        PublicKey::from_slice(&row.get::<Vec<u8>, _>("comm_pub_key")).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: format!("Invalid comm_pub_key: {}", e),
                attribute: "comm_pub_key".into(),
            }
        })?;

    bead.committed_metadata.min_target =
        CompactTarget::from_consensus(row.get::<u32, _>("min_target"));
    bead.committed_metadata.weak_target =
        CompactTarget::from_consensus(row.get::<u32, _>("weak_target"));
    bead.committed_metadata.miner_ip = row.get("miner_ip");

    let start_ts = row.get::<u32, _>("start_timestamp");
    bead.committed_metadata.start_timestamp =
        MedianTimePast::from_u32(start_ts).map_err(|e| DBErrors::TupleAttributeParsingError {
            error: format!("Invalid start_timestamp value {}: {}", start_ts, e),
            attribute: "start_timestamp".into(),
        })?;

    let broadcast_ts = row.get::<u32, _>("broadcast_timestamp");
    bead.uncommitted_metadata.broadcast_timestamp = MedianTimePast::from_u32(broadcast_ts)
        .map_err(|e| DBErrors::TupleAttributeParsingError {
            error: format!("Invalid broadcast_timestamp value {}: {}", broadcast_ts, e),
            attribute: "broadcast_timestamp".into(),
        })?;

    bead.uncommitted_metadata.extra_nonce_1 =
        u64::from_str_radix(&row.get::<String, _>("extranonce1"), 16).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "extranonce1".into(),
            }
        })?;
    bead.uncommitted_metadata.extra_nonce_2 =
        u64::from_str_radix(&row.get::<String, _>("extranonce2"), 16).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "extranonce2".into(),
            }
        })?;

    bead.uncommitted_metadata.signature =
        Signature::from_slice(&row.get::<Vec<u8>, _>("signature")).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: format!("Invalid signature: {}", e),
                attribute: "signature".into(),
            }
        })?;

    Ok(bead)
}
//Fetching single bead
pub async fn fetch_bead_by_bead_hash(
    db_connection_arc: &Pool<Sqlite>,
    bead_hash: BlockHash,
) -> Result<Option<Bead>, DBErrors> {
    let mut fetched_bead: Bead = Bead::default();
    let mut bead_id = 0;
    match sqlx::query("SELECT * FROM bead WHERE hash = ?")
        .bind(bead_hash.to_byte_array().to_vec())
        .map(|row: sqlx::sqlite::SqliteRow| {
            let id = row.get::<i32, _>("id");
            let version = BlockVersion::from_consensus(row.get::<i32, _>("nVersion"));
            let prev_block_hash = match row.get::<Vec<u8>, _>("hashPrevBlock").try_into() {
                Ok(arr) => BlockHash::from_byte_array(arr),
                Err(_) => {
                    return Err(DBErrors::TupleAttributeParsingError {
                        error: "Invalid hash length".to_string(),
                        attribute: "PrevBlockHashhash".to_string(),
                    });
                }
            };
            let merkle_hash = match row.get::<Vec<u8>, _>("hashMerkleRoot").try_into() {
                Ok(arr) => TxMerkleNode::from_byte_array(arr),
                Err(_) => {
                    return Err(DBErrors::TupleAttributeParsingError {
                        error: "Invalid hash length".to_string(),
                        attribute: "Merkle root".to_string(),
                    });
                }
            };
            let ntime = BlockTime::from_u32(row.get::<u32, _>("nTime"));
            let nbits = CompactTarget::from_consensus(row.get::<u32, _>("nBits"));
            let nonce = row.get::<u32, _>("nNonce");
            let payout_address_bytes = row.get::<Vec<u8>, _>("payout_address");
            let payout_address = std::str::from_utf8(&payout_address_bytes)
                .map_err(|_| DBErrors::TupleAttributeParsingError {
                    error: "Invalid UTF-8 in payout_address".to_string(),
                    attribute: "payout_address".to_string(),
                })?
                .to_string();
            let start_ts_val = row.get::<u32, _>("start_timestamp");
            let start_timestamp = MedianTimePast::from_u32(start_ts_val).map_err(|e| {
                DBErrors::TupleAttributeParsingError {
                    error: format!("Invalid timestamp value {}: {}", start_ts_val, e),
                    attribute: "start_timestamp".to_string(),
                }
            })?;
            let pub_key =
                PublicKey::from_slice(&row.get::<Vec<u8>, _>("comm_pub_key")).map_err(|e| {
                    DBErrors::TupleAttributeParsingError {
                        error: format!("Invalid public key: {}", e),
                        attribute: "comm_pub_key".to_string(),
                    }
                })?;
            let min_target = CompactTarget::from_consensus(row.get::<u32, _>("min_target"));
            let weak_target = CompactTarget::from_consensus(row.get::<u32, _>("weak_target"));
            let miner_ip = row.get::<String, _>("miner_ip");
            let extranonce_1 = u64::from_str_radix(&row.get::<String, _>("extranonce1"), 16)
                .map_err(|e| DBErrors::TupleAttributeParsingError {
                    error: e.to_string(),
                    attribute: "extranonce1".to_string(),
                })?;
            let extranonce_2 = u64::from_str_radix(&row.get::<String, _>("extranonce2"), 16)
                .map_err(|e| DBErrors::TupleAttributeParsingError {
                    error: e.to_string(),
                    attribute: "extranonce2".to_string(),
                })?;
            let broadcast_timestamp = MedianTimePast::from_u32(
                row.get::<u32, _>("broadcast_timestamp"),
            )
            .map_err(|e| DBErrors::TupleAttributeParsingError {
                error: e.to_string(),
                attribute: "broadcast_timestamp".to_string(),
            })?;
            let signature =
                Signature::from_slice(&row.get::<Vec<u8>, _>("signature")).map_err(|e| {
                    DBErrors::TupleAttributeParsingError {
                        error: e.to_string(),
                        attribute: "signature".to_string(),
                    }
                })?;
            bead_id = id;
            fetched_bead.block_header.version = version;
            fetched_bead.block_header.bits = nbits;
            fetched_bead.block_header.time = ntime;
            fetched_bead.committed_metadata.payout_address = payout_address;
            fetched_bead.block_header.prev_blockhash = prev_block_hash;
            fetched_bead.block_header.nonce = nonce;
            fetched_bead.block_header.merkle_root = merkle_hash;
            fetched_bead.committed_metadata.comm_pub_key = pub_key;
            fetched_bead.committed_metadata.miner_ip = miner_ip;
            fetched_bead.committed_metadata.min_target = min_target;
            fetched_bead.committed_metadata.start_timestamp = start_timestamp;
            fetched_bead.committed_metadata.weak_target = weak_target;
            fetched_bead.uncommitted_metadata.broadcast_timestamp = broadcast_timestamp;
            fetched_bead.uncommitted_metadata.extra_nonce_1 = extranonce_1;
            fetched_bead.uncommitted_metadata.extra_nonce_2 = extranonce_2;
            fetched_bead.uncommitted_metadata.signature = signature;
            Ok(())
        })
        .fetch_optional(&*db_connection_arc)
        .await
    {
        Ok(_rows) => {
            if _rows.is_none() == false {
                trace!(bead_hash = %bead_hash, "Bead fetched successfully");
            } else {
                trace!(bead_hash = %bead_hash, "No such bead exists");
            }
        }
        Err(error) => {
            return Err(DBErrors::TupleNotFetched {
                error: error.to_string(),
            });
        }
    };
    let rows =
        match sqlx::query("SELECT  txid as txid, bead_id FROM Transactions WHERE bead_id = ?")
            .bind(bead_id)
            .fetch_all(&*db_connection_arc)
            .await
        {
            Ok(rows) => rows,
            Err(error) => {
                return Err(DBErrors::TupleNotFetched {
                    error: error.to_string(),
                });
            }
        };
    //Fetching parent timestamps from DB
    let parent_timestamp_rows =
        match sqlx::query("SELECT  parent,child,timestamp FROM ParentTimestamps WHERE child = ?")
            .bind(bead_id)
            .fetch_all(&*db_connection_arc)
            .await
        {
            Ok(rows) => rows,
            Err(error) => {
                return Err(DBErrors::TupleNotFetched {
                    error: error.to_string(),
                });
            }
        };
    for parent_beads in parent_timestamp_rows {
        let parent_timestamp = parent_beads.get::<u32, _>("timestamp");
        let parent_bead_id = parent_beads.get::<i64, _>("parent");
        //Fetching parent_bead from DB
        let parent_bead_hash_raw_bytes = match sqlx::query("SELECT  hash FROM Bead WHERE id = ?")
            .bind(parent_bead_id)
            .fetch_one(&*db_connection_arc)
            .await
        {
            Ok(bead_tuple) => bead_tuple.get::<Vec<u8>, _>("hash"),
            Err(error) => {
                return Err(DBErrors::TupleNotFetched {
                    error: error.to_string(),
                });
            }
        };
        let parent_blockhash = match parent_bead_hash_raw_bytes.try_into() {
            Ok(arr) => BlockHash::from_byte_array(arr),
            Err(_) => {
                return Err(DBErrors::TupleAttributeParsingError {
                    error: "An error occurred while converting fetched bytes from DB to block hash"
                        .to_string(),
                    attribute: "Parent block hash bytes".to_string(),
                });
            }
        };
        //Extending parent bead timestamp
        let parent_ts = MedianTimePast::from_u32(parent_timestamp).map_err(|e| {
            DBErrors::TupleAttributeParsingError {
                error: format!("Invalid parent timestamp value {}: {}", parent_timestamp, e),
                attribute: "parent_bead_timestamps".to_string(),
            }
        })?;
        fetched_bead
            .committed_metadata
            .parent_bead_timestamps
            .0
            .push(parent_ts);
        //Extending parent committment by parent hash
        fetched_bead
            .committed_metadata
            .parents
            .insert(parent_blockhash);
    }
    for tx_row in rows {
        let _txid = tx_row.get::<Vec<u8>, _>("txid");
        let raw_tx_id = match _txid.clone().try_into() {
            Ok(arr) => Txid::from_byte_array(arr),
            Err(_) => {
                return Err(DBErrors::TupleAttributeParsingError {
                    error: "Invalid hash length".to_string(),
                    attribute: "Txid".to_string(),
                });
            }
        };
        fetched_bead
            .committed_metadata
            .transaction_ids
            .0
            .push(raw_tx_id);
    }

    Ok(Some(fetched_bead))
}
#[cfg(test)]
#[allow(unused)]
pub mod test {
    use super::*;
    use serde_json::json;
    use sqlx::{sqlite::SqliteConnectOptions, SqlitePool};
    use std::collections::{HashMap, HashSet};
    use std::{fs, path::Path, str::FromStr};
    const TEST_DB_URL: &str = "sqlite::memory:";
    use crate::{
        braid,
        utils::test_utils::test_utility_functions::{
            emit_bead, loading_braid_from_file, BRAIDTESTDIRECTORY,
        },
    };
    pub async fn test_db_initializer() -> Pool<Sqlite> {
        let test_pool_settings = SqliteConnectOptions::from_str(TEST_DB_URL)
            .unwrap()
            .foreign_keys(true)
            .with_regexp()
            .journal_mode(sqlx::sqlite::SqliteJournalMode::Wal);
        let test_pool = SqlitePool::connect_with(test_pool_settings).await.unwrap();
        let schema_path = std::env::current_dir().unwrap().join("src/db/schema.sql");
        let schema_sql = fs::read_to_string(&schema_path).unwrap();

        let setup_result = sqlx::query(&schema_sql.as_str()).execute(&test_pool).await;

        match setup_result {
            Ok(_) => {
                info!("Test Schema setup success");
            }
            Err(error) => {
                panic!("{:?}", error);
            }
        }

        test_pool
    }

    #[tokio::test]
    async fn test_batch_insertion_beads() {
        let test_pool = test_db_initializer().await;
        let ancestors = std::env::current_dir().unwrap();
        let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
        let parent_directory = ancestors_directory[1];
        let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
        let file_path = test_absolute_path.join("random2.json");
        let (current_file_braid, _file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());

        let mut bead_insert_data =
            BeadInsertData::resolve_many(&current_file_braid, current_file_braid.beads.iter())
                .expect("resolve_many failed: a bead or parent was missing from the braid index");
        assert_eq!(
            bead_insert_data.len(),
            current_file_braid.beads.len(),
            "resolve_many dropped beads"
        );
        // Splitting a dummy orphan bead from all the beads in the existing braid test file
        // for testing the orphan insertions as well .
        let split_at = bead_insert_data.len().saturating_sub(1);
        let orphans = bead_insert_data.split_off(split_at);
        let beads = bead_insert_data;

        // Drive the real batched-insert code path over the in-memory test pool.
        let (_db_tx, db_rx) = tokio::sync::mpsc::channel::<BraidpoolDBTypes>(DB_CHANNEL_CAPACITY);
        let handler = DBHandler {
            receiver: db_rx,
            db_connection_pool: test_pool.clone(),
        };
        handler
            .insert_beads_batch(beads, orphans)
            .await
            .expect("Batch insertion via production path failed");

        // Expected row counts derived directly from the braid.
        let expected_beads = current_file_braid.beads.len();
        let expected_txs: usize = current_file_braid
            .beads
            .iter()
            .map(|b| b.committed_metadata.transaction_ids.0.len())
            .sum();
        // Relatives and ParentTimestamps are both produced from `resolve_parents`,
        // so they share the same expected cardinality.
        let expected_relatives: usize = current_file_braid
            .beads
            .iter()
            .map(|b| current_file_braid.resolve_parents(b).unwrap().len())
            .sum();

        let bead_count: i64 = sqlx::query_scalar("SELECT COUNT(*) FROM bead")
            .fetch_one(&test_pool)
            .await
            .unwrap();
        assert_eq!(bead_count as usize, expected_beads, "Bead count mismatch");

        let tx_count: i64 = sqlx::query_scalar("SELECT COUNT(*) FROM Transactions")
            .fetch_one(&test_pool)
            .await
            .unwrap();
        assert_eq!(
            tx_count as usize, expected_txs,
            "Transactions count mismatch"
        );

        let relatives_count: i64 = sqlx::query_scalar("SELECT COUNT(*) FROM Relatives")
            .fetch_one(&test_pool)
            .await
            .unwrap();
        assert_eq!(
            relatives_count as usize, expected_relatives,
            "Relatives count mismatch"
        );

        let parent_ts_count: i64 = sqlx::query_scalar("SELECT COUNT(*) FROM ParentTimestamps")
            .fetch_one(&test_pool)
            .await
            .unwrap();
        assert_eq!(
            parent_ts_count as usize, expected_relatives,
            "ParentTimestamps count mismatch"
        );

        for bead in current_file_braid.beads.iter() {
            let fetched = fetch_bead_by_bead_hash(&test_pool, bead.block_header.block_hash())
                .await
                .unwrap()
                .unwrap_or_else(|| panic!("Bead not found: {}", bead.block_header.block_hash()));

            assert_eq!(
                fetched.block_header.block_hash().to_string(),
                bead.block_header.block_hash().to_string()
            );

            assert_eq!(
                fetched.committed_metadata.parents.len(),
                bead.committed_metadata.parents.len(),
                "Parent count mismatch for bead {}",
                bead.block_header.block_hash()
            );
        }
    }
}
