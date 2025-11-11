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
    min_target, weak_target, miner_ip, extranonce1,extranonce2,
    broadcast_timestamp, signature
)
VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,?);

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
";
#[derive(Debug)]
pub struct DBHandler {
    //Query reciever inherit to handler only
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
                            transaction_tuples.push(((*bead_id as u64), bead_tx.to_string()));
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

pub async fn fetch_bead_by_bead_hash(
    db_connection_arc: Arc<Mutex<Pool<Sqlite>>>,
    bead_hash: BlockHash,
) -> Result<Option<Bead>, DBErrors> {
    let mut bead_id = -1;
    let mut fetched_bead: Bead = Bead::default();
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
            let signture = Signature::from_slice(&row.get::<Vec<u8>, _>("signature")).unwrap();
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
            fetched_bead.uncommitted_metadata.signature = signture;
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
    // println!("bead id {}", bead_id);
    if bead_id != -1 {
        //Fetching transactions from DB using unhex to get raw hex from blob
        let rows = match sqlx::query(
            "SELECT  unhex(txid) as txid,bead_id FROM Transactions WHERE bead_id = ?",
        )
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
        let parent_timestamp_rows = match sqlx::query(
            "SELECT  parent,child,timestamp FROM ParentTimestamps WHERE child = ?",
        )
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
            let parent_bead_hash_str = match sqlx::query("SELECT  hash FROM Beads WHERE id = ?")
                .bind(parent_bead_id)
                .fetch_one(&db_connection_arc.lock().await.clone())
                .await
            {
                Ok(bead_tuple) => bead_tuple.get::<String, _>("hash"),
                Err(error) => {
                    return Err(DBErrors::TupleNotFetched {
                        error: error.to_string(),
                    });
                }
            };
            let mut parent_hash_raw_bytes: [u8; 32] = [0u8; 32];
            let _parent_decode_res =
                hex::decode_to_slice(parent_bead_hash_str, &mut parent_hash_raw_bytes);
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
                .insert(BlockHash::from_byte_array(parent_hash_raw_bytes));
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
    } else {
        return Ok(None);
    }
    Ok(Some(fetched_bead))
}
#[cfg(test)]
#[allow(unused)]
pub mod test {
    use super::*;
    use serde_json::json;
    use sqlx::{sqlite::SqliteConnectOptions, SqlitePool};
    use std::{fs, str::FromStr};
    const TEST_DB_URL: &str = "sqlite::memory:";
    use crate::{braid, utils::test_utils::test_utility_functions::emit_bead};
    async fn insert_bead(
        test_conn: Pool<Sqlite>,
        test_braid: Arc<RwLock<braid::Braid>>,
    ) -> Result<BlockHash, DBErrors> {
        let test_bead = emit_bead();
        let mut test_braid_data = test_braid.write().await;
        let status = test_braid_data.extend(&test_bead);
        let mut braid_parent_set: HashMap<usize, HashSet<usize>> = HashMap::new();
        //Constructing the parent set
        for bead in test_braid_data.beads.iter().enumerate() {
            let parent_beads = &bead.1.committed_metadata.parents;
            braid_parent_set.insert(bead.0, HashSet::new());
            for parent_bead_hash in parent_beads.iter() {
                let current_parent_bead_index = test_braid_data
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
            &test_braid_data,
            test_bead.block_header.block_hash(),
            &mut ancestor_mapping,
            &braid_parent_set,
        );
        //Considering the index of the beads in braid will be same as the (insertion ids-1)
        let bead_id = test_braid_data
            .bead_index_mapping
            .get(&test_bead.block_header.block_hash())
            .unwrap();
        let current_bead_parent_set = braid_parent_set.get(&(bead_id)).unwrap();
        let mut relative_tuples: Vec<(u64, u64)> = Vec::new();
        let mut parent_timestamp_tuples: Vec<(u64, u64, u64)> = Vec::new();
        let mut transaction_tuples: Vec<(u64, String)> = Vec::new();
        //Constructing relatives and parent_timestamps
        for parent_bead in current_bead_parent_set {
            relative_tuples.push(((*parent_bead as u64), (*bead_id as u64)));
            let current_parent_timestamp = test_braid_data
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
        for bead_tx in test_bead.committed_metadata.transaction_ids.0.iter() {
            transaction_tuples.push(((*bead_id as u64), bead_tx.to_string()));
        }
        //Inserting dummy test transaction
        transaction_tuples.push((
            0,
            "55089847fc2828db9e7ab0691e618db57784e8808bb589fd2fe1d276a922b454".to_string(),
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
                    "parent":r.1,
                    "child":r.0
                })
            })
            .collect::<Vec<_>>();
        let test_tx_json = serde_json::to_string(&transactions_values).unwrap();
        let test_relative_json = serde_json::to_string(&relatives_values).unwrap();
        let test_parent_timestamp_json = serde_json::to_string(&parent_timestamps_values).unwrap();
        let hex_converted_extranonce_1 =
            hex::encode(test_bead.uncommitted_metadata.extra_nonce_1.to_be_bytes());
        let hex_converted_extranonce_2 =
            hex::encode(test_bead.uncommitted_metadata.extra_nonce_2.to_be_bytes());
        let block_header_bytes = test_bead.block_header.block_hash().to_byte_array().to_vec();
        let prev_block_hash_bytes = test_bead
            .block_header
            .prev_blockhash
            .to_byte_array()
            .to_vec();
        let merkel_root_bytes = test_bead.block_header.merkle_root.to_byte_array().to_vec();
        let payout_addr_bytes = test_bead
            .committed_metadata
            .payout_address
            .as_bytes()
            .to_vec();
        let public_key_bytes = test_bead.committed_metadata.comm_pub_key.to_vec();
        let signature_bytes = test_bead.uncommitted_metadata.signature.to_vec();
        //All fields are in be format
        if let Err(e) = sqlx::query(&INSERT_QUERY)
            .bind(*bead_id as i64)
            .bind(block_header_bytes)
            .bind(test_bead.block_header.version.to_consensus())
            .bind(prev_block_hash_bytes)
            .bind(merkel_root_bytes)
            .bind(test_bead.block_header.time.to_u32())
            .bind(test_bead.block_header.bits.to_consensus())
            .bind(test_bead.block_header.nonce)
            .bind(payout_addr_bytes)
            .bind(test_bead.committed_metadata.start_timestamp.to_u32())
            .bind(public_key_bytes)
            .bind(
                test_bead
                    .committed_metadata
                    .min_target
                    .to_consensus()
                    .to_string(),
            )
            .bind(test_bead.committed_metadata.weak_target.to_consensus())
            .bind(test_bead.committed_metadata.miner_ip)
            .bind(hex_converted_extranonce_1.to_string())
            .bind(hex_converted_extranonce_2.to_string())
            .bind(test_bead.uncommitted_metadata.broadcast_timestamp.to_u32())
            .bind(signature_bytes)
            .bind(test_tx_json)
            .bind(test_relative_json)
            .bind(test_parent_timestamp_json)
            .execute(&test_conn)
            .await
        {
            println!("Transaction failed to commit rolling back due to - {:?}", e);
            match sqlx::query("ROLLBACK;").execute(&test_conn).await {
                Ok(_query_res) => {
                    println!("Transaction rolled back successfully - {:?}", _query_res);
                }
                Err(error) => {
                    return Err(DBErrors::TransactionNotRolledBack {
                        error: error.to_string(),
                        query: "Combined insert transaction".to_string(),
                    })
                }
            };
            return Err(DBErrors::InsertionTransactionNotCommitted {
                error: e.to_string(),
                query_name: "Combined insert transaction".to_string(),
            });
        }
        Ok(test_bead.block_header.block_hash())
    }

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
    async fn test_insert_bead() {
        let pool = test_db_initializer().await;
        let genesis_beads = Vec::from([]);
        // Initializing the braid object with read write lock
        //for supporting concurrent readers and single writer
        let test_braid: Arc<RwLock<braid::Braid>> =
            Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
        let res = insert_bead(pool.clone(), test_braid.clone()).await;
        let fetched_bead =
            fetch_bead_by_bead_hash(Arc::new(Mutex::new(pool)), res.clone().unwrap())
                .await
                .unwrap();
        println!("Option fetched {:?}", fetched_bead);
        assert_eq!(
            fetched_bead.unwrap().block_header.block_hash().to_string(),
            res.unwrap().to_string()
        );
    }
}
