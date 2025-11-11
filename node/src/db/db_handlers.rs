use crate::{
    bead::Bead,
    braid::{consensus_functions, Braid},
    db::{init_db::init_db, BraidpoolDBTypes, InsertTupleTypes},
    error::DBErrors,
};
use bitcoin::{
    absolute::MedianTimePast, ecdsa::Signature, BlockHash, BlockTime, BlockVersion, CompactTarget,
    PublicKey, TxMerkleNode, Txid,
};
use futures::lock::Mutex;
use num::ToPrimitive;
use serde_json::json;
use sqlx::{Pool, Row, Sqlite};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use tokio::sync::{
    mpsc::{Receiver, Sender},
    RwLock,
};
const DB_CHANNEL_CAPACITY: usize = 1024;
const INSERT_QUERY: &'static str = "
INSERT INTO bead (
    id, hash, nVersion, hashPrevBlock, hashMerkleRoot, nTime,
    nBits, nNonce, payout_address, start_timestamp, comm_pub_key,
    min_target, weak_target, miner_ip, extranonce1, extranonce2,
    broadcast_timestamp, signature
)
VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,?);

INSERT INTO Transactions (bead_id, txid)
SELECT
    json_extract(value, '$.bead_id') AS bead_id,
    unhex(json_extract(value, '$.txid')) AS txid
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
";
#[derive(Debug)]
pub struct DBHandler {
    //Query receiver inherit to handler only
    receiver: Receiver<BraidpoolDBTypes>,
    //Shared across tasks for accessing DB after contention using `Mutex`
    pub db_connection_pool: Arc<Mutex<Pool<Sqlite>>>,
    local_braid_arc: Arc<RwLock<Braid>>,
}
impl DBHandler {
    pub async fn new(
        local_braid_arc: Arc<RwLock<Braid>>,
    ) -> Result<(Self, Sender<BraidpoolDBTypes>), DBErrors> {
        log::info!("Initializing Schema for persistent DB");
        let connection = match init_db().await {
            Ok(conn) => conn,
            Err(error) => {
                log::error!("An error occurred while initializing and establishing connection with local DB {:?}.", error);
                return Err(DBErrors::ConnectionToDBNotEstablished {
                    error: error.to_string(),
                });
            }
        };
        let (db_handler_tx, db_handler_rx) = tokio::sync::mpsc::channel(DB_CHANNEL_CAPACITY);
        Ok((
            Self {
                receiver: db_handler_rx,
                db_connection_pool: Arc::new(Mutex::new(connection)),
                local_braid_arc: local_braid_arc,
            },
            db_handler_tx,
        ))
    }
    //Insertion handlers private
    pub async fn insert_bead(
        &self,
        bead: Bead,
        txs_json: String,
        relative_json: String,
        parent_timestamp_json: String,
        _ancestor_mapping: &HashMap<usize, HashSet<usize>>,
        bead_id: &usize,
    ) -> Result<(), DBErrors> {
        log::info!("Sequential insertion query received from the query handler");
        let hex_converted_extranonce_1 =
            hex::encode(bead.uncommitted_metadata.extra_nonce_1.to_be_bytes());
        let hex_converted_extranonce_2 =
            hex::encode(bead.uncommitted_metadata.extra_nonce_2.to_be_bytes());
        let block_header_bytes = bead.block_header.block_hash().to_byte_array().to_vec();
        let prev_block_hash_bytes = bead.block_header.prev_blockhash.to_byte_array().to_vec();
        let merkel_root_bytes = bead.block_header.merkle_root.to_byte_array().to_vec();
        let payout_addr_bytes = bead.committed_metadata.payout_address.as_bytes().to_vec();
        let public_key_bytes = bead.committed_metadata.comm_pub_key.to_vec();
        let signature_bytes = bead.uncommitted_metadata.signature.to_vec();
        let mut conn = self.db_connection_pool.lock().await.begin().await.unwrap();
        //All fields are in be format
        if let Err(e) = sqlx::query(&INSERT_QUERY)
            .bind(*bead_id as i64)
            .bind(block_header_bytes)
            .bind(bead.block_header.version.to_consensus())
            .bind(prev_block_hash_bytes)
            .bind(merkel_root_bytes)
            .bind(bead.block_header.time.to_u32())
            .bind(bead.block_header.bits.to_consensus())
            .bind(bead.block_header.nonce)
            .bind(payout_addr_bytes)
            .bind(bead.committed_metadata.start_timestamp.to_u32())
            .bind(public_key_bytes)
            .bind(bead.committed_metadata.min_target.to_consensus())
            .bind(bead.committed_metadata.weak_target.to_consensus())
            .bind(bead.committed_metadata.miner_ip)
            .bind(hex_converted_extranonce_1.to_string())
            .bind(hex_converted_extranonce_2.to_string())
            .bind(bead.uncommitted_metadata.broadcast_timestamp.to_u32())
            .bind(signature_bytes)
            .bind(txs_json)
            .bind(relative_json)
            .bind(parent_timestamp_json)
            .execute(&mut *conn)
            .await
        {
            log::error!("Transaction failed to commit rolling back due to - {:?}", e);
            match conn.rollback().await {
                Ok(_) => {
                    log::info!("Transaction rollbacked successfully");
                    return Ok(());
                }
                Err(error) => {
                    log::error!("An error occurred while rolling back the transaction");
                    return Err(DBErrors::TransactionNotRolledBack {
                        error: error.to_string(),
                        query: "Insertion of Bead".to_string(),
                    });
                }
            }
        }
        match conn.commit().await {
            Ok(_) => {
                log::info!("All related insertions committed successfully");
            }
            Err(error) => {
                log::error!("An error occurred while committing transaction");
                return Err(DBErrors::InsertionTransactionNotCommitted {
                    error: error.to_string(),
                    query_name: "Combined insert transaction".to_string(),
                });
            }
        };
        Ok(())
    }
    //Individual insertion operations
    pub async fn insert_query_handler(&mut self) {
        log::info!("Query handler task started");
        while let Some(query_request) = self.receiver.recv().await {
            match query_request {
                BraidpoolDBTypes::InsertTupleTypes { query } => match query {
                    InsertTupleTypes::InsertBeadSequentially { bead_to_insert } => {
                        let braid_data = self.local_braid_arc.read().await;
                        let mut braid_parent_set: HashMap<usize, HashSet<usize>> = HashMap::new();
                        //Constructing the parent set
                        for bead in braid_data.beads.iter().enumerate() {
                            let parent_beads = &bead.1.committed_metadata.parents;
                            braid_parent_set.insert(bead.0, HashSet::new());
                            for parent_bead_hash in parent_beads.iter() {
                                let current_parent_bead_index = braid_data
                                    .bead_index_mapping
                                    .get(&*parent_bead_hash)
                                    .unwrap();
                                if let Some(value) = braid_parent_set.get_mut(&bead.0) {
                                    value.insert(*current_parent_bead_index);
                                }
                            }
                        }
                        //Constructing ancestor set, children set will be empty as it will become the next tip
                        let mut ancestor_mapping: HashMap<usize, HashSet<usize>> = HashMap::new();
                        consensus_functions::updating_ancestors(
                            &braid_data,
                            bead_to_insert.block_header.block_hash(),
                            &mut ancestor_mapping,
                            &braid_parent_set,
                        );
                        //Considering the index of the beads in braid will be same as the (insertion ids-1)
                        let bead_id = braid_data
                            .bead_index_mapping
                            .get(&bead_to_insert.block_header.block_hash())
                            .unwrap();
                        let current_bead_parent_set = braid_parent_set.get(&(bead_id)).unwrap();

                        let mut relative_tuples: Vec<(u64, u64)> = Vec::new();
                        let mut parent_timestamp_tuples: Vec<(u64, u64, u64)> = Vec::new();
                        let mut transaction_tuples: Vec<(u64, String)> = Vec::new();
                        //Constructing relatives and parent_timestamps
                        for parent_bead in current_bead_parent_set {
                            relative_tuples.push(((*parent_bead as u64), (*bead_id as u64)));
                            let current_parent_timestamp = braid_data
                                .beads
                                .get(*parent_bead)
                                .unwrap()
                                .committed_metadata
                                .start_timestamp;
                            parent_timestamp_tuples.push((
                                (*parent_bead as u64),
                                (*bead_id as u64),
                                current_parent_timestamp.to_u32().to_u64().unwrap(),
                            ));
                        }
                        for bead_tx in bead_to_insert.committed_metadata.transaction_ids.0.iter() {
                            transaction_tuples
                                .push(((*bead_id as u64), hex::encode(bead_tx.to_byte_array())));
                        }
                        //Constructing json bindings
                        let transactions_values = transaction_tuples
                            .iter()
                            .map(|t| {
                                json!({
                                    "txid":t.1,
                                    "bead_id":t.0
                                })
                            })
                            .collect::<Vec<_>>();
                        let parent_timestamps_values = parent_timestamp_tuples
                            .iter()
                            .map(|p| {
                                json!({
                                    "child":p.1,
                                    "parent":p.0,
                                    "timestamp":p.2
                                })
                            })
                            .collect::<Vec<_>>();

                        let relatives_values = relative_tuples
                            .iter()
                            .map(|r| {
                                json!({
                                    "parent":r.0,
                                    "child":r.1
                                })
                            })
                            .collect::<Vec<_>>();
                        let txs_json = serde_json::to_string(&transactions_values).unwrap();
                        let relative_json = serde_json::to_string(&relatives_values).unwrap();
                        let parent_timestamp_json =
                            serde_json::to_string(&parent_timestamps_values).unwrap();

                        match self
                            .insert_bead(
                                bead_to_insert,
                                txs_json,
                                relative_json,
                                parent_timestamp_json,
                                &ancestor_mapping,
                                bead_id,
                            )
                            .await
                        {
                            Ok(_) => {
                                log::info!("Insertion query handled");
                            }
                            Err(error) => {
                                log::error!("Error occurred while dealing with DB - {:?}", error);
                                continue;
                            }
                        };
                    }
                },
            }
        }
    }
}
//Fetching beads in batch
pub async fn fetch_beads_in_batch(
    db_pool: Arc<Mutex<Pool<Sqlite>>>,
    batch_size: u32,
) -> Result<Vec<Bead>, DBErrors> {
    let mut fetched_beads = Vec::new();
    let conn = db_pool.lock().await.clone();

    let total_rows: u32 = sqlx::query("SELECT COUNT(*) as row_cnt FROM BEAD")
        .fetch_one(&conn)
        .await
        .map_err(|e| DBErrors::TupleNotFetched {
            error: e.to_string(),
        })?
        .get("row_cnt");

    log::info!(
        "Number of beads present locally in persistent DB - {:?}",
        total_rows
    );
    if total_rows == 0 {
        return Ok(vec![]);
    }

    let num_batches = (total_rows + batch_size - 1) / batch_size;

    for batch_num in 0..num_batches {
        let offset = batch_num * batch_size;
        let rows = sqlx::query("SELECT * FROM BEAD LIMIT ? OFFSET ?")
            .bind(batch_size)
            .bind(offset)
            .fetch_all(&conn)
            .await
            .map_err(|e| DBErrors::TupleNotFetched {
                error: e.to_string(),
            })?;
        for row in rows {
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
                PublicKey::from_slice(&row.get::<Vec<u8>, _>("comm_pub_key")).map_err(|_| {
                    DBErrors::TupleAttributeParsingError {
                        error: "Invalid comm_pub_key".into(),
                        attribute: "comm_pub_key".into(),
                    }
                })?;

            bead.committed_metadata.min_target =
                CompactTarget::from_consensus(row.get::<u32, _>("min_target"));
            bead.committed_metadata.weak_target =
                CompactTarget::from_consensus(row.get::<u32, _>("weak_target"));
            bead.committed_metadata.miner_ip = row.get("miner_ip");

            bead.committed_metadata.start_timestamp =
                MedianTimePast::from_u32(row.get::<u32, _>("start_timestamp")).unwrap();

            bead.uncommitted_metadata.broadcast_timestamp =
                MedianTimePast::from_u32(row.get::<u32, _>("broadcast_timestamp")).unwrap();

            bead.uncommitted_metadata.extra_nonce_1 =
                u32::from_str_radix(&row.get::<String, _>("extranonce1"), 16).unwrap();
            bead.uncommitted_metadata.extra_nonce_2 =
                u32::from_str_radix(&row.get::<String, _>("extranonce2"), 16).unwrap();

            bead.uncommitted_metadata.signature =
                Signature::from_slice(&row.get::<Vec<u8>, _>("signature")).unwrap();

            let current_bead_id = row.get::<i32, _>("id");

            let tx_rows = sqlx::query("SELECT txid as txid FROM Transactions WHERE bead_id = ?")
                .bind(current_bead_id)
                .fetch_all(&conn)
                .await
                .map_err(|e| DBErrors::TupleNotFetched {
                    error: e.to_string(),
                })?;

            for tx in tx_rows {
                let tx_bytes: Vec<u8> = tx.get("txid");
                let arr: [u8; 32] =
                    tx_bytes
                        .try_into()
                        .map_err(|_| DBErrors::TupleAttributeParsingError {
                            error: "Invalid Txid length".into(),
                            attribute: "txid".into(),
                        })?;
                bead.committed_metadata
                    .transaction_ids
                    .0
                    .push(Txid::from_byte_array(arr));
            }

            let parent_rows =
                sqlx::query("SELECT parent, timestamp FROM ParentTimestamps WHERE child = ?")
                    .bind(current_bead_id)
                    .fetch_all(&conn)
                    .await
                    .map_err(|e| DBErrors::TupleNotFetched {
                        error: e.to_string(),
                    })?;

            for parent in parent_rows {
                let parent_id = parent.get::<i64, _>("parent");
                let timestamp = parent.get::<i32, _>("timestamp");

                let parent_hash_row = sqlx::query("SELECT hash FROM BEAD WHERE id = ?")
                    .bind(parent_id)
                    .fetch_one(&conn)
                    .await
                    .map_err(|e| DBErrors::TupleNotFetched {
                        error: e.to_string(),
                    })?;

                match parent_hash_row.get::<Vec<u8>, _>("hash").try_into() {
                    Ok(arr) => {
                        bead.committed_metadata
                            .parents
                            .insert(BlockHash::from_byte_array(arr));
                    }
                    Err(_) => {
                        return Err(DBErrors::TupleAttributeParsingError {
                            error: "Invalid hash length".to_string(),
                            attribute: "Parent bead hash".to_string(),
                        });
                    }
                };

                bead.committed_metadata
                    .parent_bead_timestamps
                    .0
                    .push(MedianTimePast::from_u32(timestamp as u32).unwrap());
            }

            fetched_beads.push(bead);
        }
    }

    Ok(fetched_beads)
}
//Fetching single bead
pub async fn fetch_bead_by_bead_hash(
    db_connection_arc: Arc<Mutex<Pool<Sqlite>>>,
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
            let merkel_hash = match row.get::<Vec<u8>, _>("hashMerkleRoot").try_into() {
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
            let payout_address = str::from_utf8(&row.get::<Vec<u8>, _>("payout_address"))
                .unwrap()
                .to_string();

            let start_timestamp =
                MedianTimePast::from_u32(row.get::<u32, _>("start_timestamp")).unwrap();
            let pub_key = PublicKey::from_slice(&row.get::<Vec<u8>, _>("comm_pub_key")).unwrap();
            let min_target = CompactTarget::from_consensus(row.get::<u32, _>("min_target"));
            let weak_target = CompactTarget::from_consensus(row.get::<u32, _>("weak_target"));
            let miner_ip = row.get::<String, _>("miner_ip");
            let extranonce_1 =
                u32::from_str_radix(&row.get::<String, _>("extranonce1"), 16).unwrap();
            let extranonce_2 =
                u32::from_str_radix(&row.get::<String, _>("extranonce2"), 16).unwrap();
            let broadcast_timestamp =
                MedianTimePast::from_u32(row.get::<u32, _>("broadcast_timestamp")).unwrap();
            let signature = Signature::from_slice(&row.get::<Vec<u8>, _>("signature")).unwrap();
            bead_id = id;
            fetched_bead.block_header.version = version;
            fetched_bead.block_header.bits = nbits;
            fetched_bead.block_header.time = ntime;
            fetched_bead.committed_metadata.payout_address = payout_address;
            fetched_bead.block_header.prev_blockhash = prev_block_hash;
            fetched_bead.block_header.nonce = nonce;
            fetched_bead.block_header.merkle_root = merkel_hash;
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
        .fetch_optional(&db_connection_arc.lock().await.clone())
        .await
    {
        Ok(_rows) => {
            if _rows.is_some() {
                println!("Bead with given bead hash fetched successfully");
            } else {
                println!("No such bead exists");
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
            .fetch_all(&db_connection_arc.lock().await.clone())
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
            .fetch_all(&db_connection_arc.lock().await.clone())
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
        let parent_timestamp = parent_beads.get::<i32, _>("timestamp");
        let parent_bead_id = parent_beads.get::<i64, _>("parent");
        //Fetching parent_bead from DB
        let parent_bead_hash_raw_bytes = match sqlx::query("SELECT  hash FROM Bead WHERE id = ?")
            .bind(parent_bead_id)
            .fetch_one(&db_connection_arc.lock().await.clone())
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
        fetched_bead
            .committed_metadata
            .parent_bead_timestamps
            .0
            .push(MedianTimePast::from_u32(parent_timestamp as u32).unwrap());
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
        println!("{:?}", raw_tx_id);
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
                println!("Test Schema setup success");
            }
            Err(error) => {
                panic!("{:?}", error);
            }
        }

        test_pool
    }

    #[tokio::test]
    async fn test_insertion_beads() {
        let test_pool = test_db_initializer().await;
        let ancestors = std::env::current_dir().unwrap();
        let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
        let parent_directory = ancestors_directory[1];
        let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
        let file_path = test_absolute_path.join("random2.json");
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        for bead in current_file_braid.beads.iter() {
            let mut braid_parent_set: HashMap<usize, HashSet<usize>> = HashMap::new();
            for bead in current_file_braid.beads.iter().enumerate() {
                let parent_beads = &bead.1.committed_metadata.parents;
                braid_parent_set.insert(bead.0, HashSet::new());
                for parent_bead_hash in parent_beads.iter() {
                    let current_parent_bead_index = current_file_braid
                        .bead_index_mapping
                        .get(&*parent_bead_hash)
                        .unwrap();
                    if let Some(value) = braid_parent_set.get_mut(&bead.0) {
                        value.insert(*current_parent_bead_index);
                    }
                }
            }
            let mut ancestor_mapping: HashMap<usize, HashSet<usize>> = HashMap::new();
            consensus_functions::updating_ancestors(
                &current_file_braid,
                bead.block_header.block_hash(),
                &mut ancestor_mapping,
                &braid_parent_set,
            );
            let bead_id = current_file_braid
                .bead_index_mapping
                .get(&bead.block_header.block_hash())
                .unwrap();
            let current_bead_parent_set = braid_parent_set.get(&(bead_id)).unwrap();
            let mut relative_tuples: Vec<(u64, u64)> = Vec::new();
            let mut parent_timestamp_tuples: Vec<(u64, u64, u64)> = Vec::new();
            let mut transaction_tuples: Vec<(u64, String)> = Vec::new();
            for parent_bead in current_bead_parent_set {
                relative_tuples.push(((*parent_bead as u64), (*bead_id as u64)));
                let current_parent_timestamp = current_file_braid
                    .beads
                    .get(*parent_bead)
                    .unwrap()
                    .committed_metadata
                    .start_timestamp;
                parent_timestamp_tuples.push((
                    (*parent_bead as u64),
                    (*bead_id as u64),
                    current_parent_timestamp.to_u32().to_u64().unwrap(),
                ));
            }
            for bead_tx in bead.committed_metadata.transaction_ids.0.iter() {
                transaction_tuples.push(((*bead_id as u64), hex::encode(bead_tx.to_byte_array())));
            }
            //Adding dummy tx
            transaction_tuples.push((
                *bead_id as u64,
                "b1a6cecc2e40e89e9e943c3c010c1f6ca6dd1530361ead7289254d929ee4eb2a".to_string(),
            ));
            let transactions_values = transaction_tuples
                .iter()
                .map(|t| {
                    json!({
                        "txid":t.1,
                        "bead_id":t.0
                    })
                })
                .collect::<Vec<_>>();
            let parent_timestamps_values = parent_timestamp_tuples
                .iter()
                .map(|p| {
                    json!({
                        "child":p.1,
                        "parent":p.0,
                        "timestamp":p.2
                    })
                })
                .collect::<Vec<_>>();

            let relatives_values = relative_tuples
                .iter()
                .map(|r| {
                    json!({
                        "parent":r.0,
                        "child":r.1
                    })
                })
                .collect::<Vec<_>>();
            let test_tx_json = serde_json::to_string(&transactions_values).unwrap();
            let test_relative_json = serde_json::to_string(&relatives_values).unwrap();
            let test_parent_timestamp_json =
                serde_json::to_string(&parent_timestamps_values).unwrap();
            let hex_converted_extranonce_1 =
                hex::encode(bead.uncommitted_metadata.extra_nonce_1.to_be_bytes());
            let hex_converted_extranonce_2 =
                hex::encode(bead.uncommitted_metadata.extra_nonce_2.to_be_bytes());
            let block_header_bytes = bead.block_header.block_hash().to_byte_array().to_vec();
            let prev_block_hash_bytes = bead.block_header.prev_blockhash.to_byte_array().to_vec();
            let merkel_root_bytes = bead.block_header.merkle_root.to_byte_array().to_vec();
            let payout_addr_bytes = bead.committed_metadata.payout_address.as_bytes().to_vec();
            let public_key_bytes = bead.committed_metadata.comm_pub_key.to_vec();
            let signature_bytes = bead.uncommitted_metadata.signature.to_vec();
            let mut test_insertion_tx = test_pool.begin().await.unwrap();
            if let Err(e) = sqlx::query(&INSERT_QUERY)
                .bind(*bead_id as i64)
                .bind(block_header_bytes)
                .bind(bead.block_header.version.to_consensus())
                .bind(prev_block_hash_bytes)
                .bind(merkel_root_bytes)
                .bind(bead.block_header.time.to_u32())
                .bind(bead.block_header.bits.to_consensus())
                .bind(bead.block_header.nonce)
                .bind(payout_addr_bytes)
                .bind(bead.committed_metadata.start_timestamp.to_u32())
                .bind(public_key_bytes)
                .bind(bead.committed_metadata.min_target.to_consensus())
                .bind(bead.committed_metadata.weak_target.to_consensus())
                .bind(bead.committed_metadata.miner_ip.clone())
                .bind(hex_converted_extranonce_1.to_string())
                .bind(hex_converted_extranonce_2.to_string())
                .bind(bead.uncommitted_metadata.broadcast_timestamp.to_u32())
                .bind(signature_bytes)
                .bind(test_tx_json)
                .bind(test_relative_json)
                .bind(test_parent_timestamp_json)
                .execute(&mut *test_insertion_tx)
                .await
            {
                println!("Transaction failed to commit rolling back due to - {:?}", e);
                match test_insertion_tx.rollback().await {
                    Ok(_) => {
                        println!("Transaction rollbacked successfully");
                        continue;
                    }
                    Err(error) => {
                        panic!(
                            "An error occurred while rolling back the transaction - {:?}",
                            error
                        )
                    }
                }
            }
            match test_insertion_tx.commit().await {
                Ok(_) => {
                    println!("All related insertions committed successfully");
                }
                Err(error) => {
                    panic!("An error occurred while committing transaction");
                }
            };
            let fetched_test_bead = fetch_bead_by_bead_hash(
                Arc::new(Mutex::new(test_pool.clone())),
                bead.block_header.block_hash(),
            )
            .await
            .unwrap();
            assert_eq!(
                fetched_test_bead
                    .unwrap()
                    .block_header
                    .block_hash()
                    .to_string(),
                bead.block_header.block_hash().to_string()
            );
        }
    }
}
