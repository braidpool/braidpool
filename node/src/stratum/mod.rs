/// Shared signal written to a miner's send channel to close the TCP connection.
pub const DISCONNECT_SIGNAL: &str = "!!!_INTERNAL_DISCONNECT_SIGNAL_!!!";

// Constants shared by child modules
const PREFIX_BYTES_SIZE: usize = 2;
const COMMITMENT_SIZE: usize = 5;
const DEFAULT_VERSION_ROLLING_MASK: u32 = 0x1FFFE000;
const UPSTREAM_EXTRANONCE1_SIZE: usize = 4;
const COMMITMENT_HISTORY_SIZE: usize = 5;

pub mod client;
pub mod connection;
pub mod job_store;
pub mod notifier;
pub mod server;
pub mod types;

// Re-exports so callers using `crate::stratum::Foo` continue to work
pub use client::DownstreamClient;
pub use connection::{ConnectionInfo, ConnectionMapping, ControlMsg, PrefixStats};
pub use job_store::GlobalJobStore;
pub use notifier::{reverse_four_byte_chunks, Notifier, NotifyCmd};
pub use server::Server;
pub use types::{
    BlockSubmissionRequest, BlockTemplate, JobDetails, JobNotification, JobNotificationResponse,
    StandardRequest, StandardResponse, StratumResponses, StratumServerConfig,
    SuggestDifficultyResponse,
};

#[allow(dead_code, unused)]
#[cfg(test)]
mod test {
    use std::{collections::HashMap, str::FromStr, sync::Arc, time::Duration};
    use std::sync::atomic::AtomicBool;
    use std::time::UNIX_EPOCH;

    use bitcoin::consensus::{serialize, Decodable};
    use bitcoin::hashes::Hash as _;
    use bitcoin::io::Cursor;
    use bitcoin::{block::Header as BlockHeader, Transaction, TxMerkleNode, Witness};
    use num::ToPrimitive;
    use serde_json::json;

    use crate::config::PoolNetwork;
    use crate::template_creator::calculate_merkle_root;
    use crate::utils::compute_block_hash;
    use crate::{SwarmHandler, TemplateId};

    use super::UPSTREAM_EXTRANONCE1_SIZE;
    use super::*;

    use crate::{
        braid,
        db::db_handlers::DBHandler,
        rpc_server::DashboardEvents,
        stratum::{ConnectionMapping, GlobalJobStore, NotifyCmd, Server, StratumServerConfig},
    };
    use bitcoin::{
        absolute::LockTime, block::Version as BlockVersion, Amount, BlockHash, OutPoint, ScriptBuf,
        Sequence, TxIn, TxOut,
    };
    use futures::lock::Mutex;
    use tokio::{
        io::{AsyncBufReadExt, AsyncWriteExt, BufReader},
        net::{TcpListener, TcpStream},
        sync::{mpsc, RwLock},
    };

    #[tokio::test]
    async fn test_connection_mapping_prefix_allocation() {
        let mut mapping = ConnectionMapping::new();

        mapping.set_upstream_extranonce("aabbccdd".to_string(), 8);

        // Allocate multiple prefixes
        let (prefix1, size1) = mapping.allocate_extranonce2_prefix();
        let (prefix2, size2) = mapping.allocate_extranonce2_prefix();
        let (prefix3, size3) = mapping.allocate_extranonce2_prefix();

        // Each prefix should be unique
        assert_ne!(prefix1, prefix2, "Prefixes should be unique");
        assert_ne!(prefix2, prefix3, "Prefixes should be unique");
        assert_ne!(prefix1, prefix3, "Prefixes should be unique");

        assert_eq!(size1, size2);
        assert_eq!(size2, size3);
    }

    #[tokio::test]
    async fn test_connection_mapping_prefix_reuse() {
        let mut mapping = ConnectionMapping::new();
        mapping.set_upstream_extranonce("aabbccdd".to_string(), 8);

        // Allocate and register a prefix
        let (prefix1, _) = mapping.allocate_extranonce2_prefix();
        let prefix1_u16 = u16::from_be_bytes([prefix1[0], prefix1[1]]);
        mapping.register_prefix("peer1".to_string(), prefix1_u16);

        // Get stats before release
        let stats_before = mapping.get_prefix_stats();
        assert_eq!(stats_before.total_assigned, 1);
        assert_eq!(stats_before.available_for_reuse, 0);

        // Release the prefix
        mapping.remove_peer("peer1");

        // Get stats after release
        let stats_after = mapping.get_prefix_stats();
        assert_eq!(stats_after.total_assigned, 0);
        assert_eq!(stats_after.available_for_reuse, 1);

        // Allocate again, this should reuse the released prefix
        let (prefix2, _) = mapping.allocate_extranonce2_prefix();
        assert_eq!(prefix1, prefix2, "Should reuse released prefix");
    }

    #[test]
    fn test_global_job_store_operations() {
        let mut store = GlobalJobStore::new(10);

        let template = BlockTemplate::default();
        let job_details = JobDetails {
            blocktemplate: template,
            coinbase1: "test_coinbase1".to_string(),
            coinbase2: "test_coinbase2".to_string(),
            coinbase_merkle_path: vec![],
            coinbase_witness_commitment: None,
            job_sent_time: 1234567890,
            is_upstream_job: false,
        };

        // Insert Braidpool job
        let job_id = store.insert(TemplateId::Braidpool(1), Arc::new(job_details.clone()));
        assert_eq!(job_id, 0, "First job ID should be 0");

        // Retrieve by job_id
        let retrieved = store.get_by_job_id(job_id);
        assert!(retrieved.is_ok(), "Should retrieve inserted job");

        // Retrieve by template_id
        let retrieved_by_template = store.get_by_template_id(&TemplateId::Braidpool(1));
        assert!(
            retrieved_by_template.is_ok(),
            "Should retrieve by template_id"
        );

        // Insert another job — different template_id, next numeric slot
        let job_id_2 = store.insert(TemplateId::Braidpool(2), Arc::new(job_details.clone()));
        assert_eq!(job_id_2, 1, "Second job ID should be 1");
    }

    #[test]
    fn test_upstream_job_storage() {
        let mut store = GlobalJobStore::new(10);

        let template = BlockTemplate::default();
        let job_details = JobDetails {
            blocktemplate: template,
            coinbase1: "upstream_coinbase1".to_string(),
            coinbase2: "upstream_coinbase2".to_string(),
            coinbase_merkle_path: vec![],
            coinbase_witness_commitment: None,
            job_sent_time: 1234567890,
            is_upstream_job: true,
        };

        let upstream_id = "upstream_job_abc123";
        store.insert(
            TemplateId::Upstream(upstream_id.to_string()),
            Arc::new(job_details),
        );

        // Retrieve by original string job_id
        let retrieved = store.get_by_string_job_id(upstream_id);
        assert!(
            retrieved.is_ok(),
            "Should retrieve upstream job by string ID"
        );

        let (retrieved_job, _template_id) = retrieved.unwrap();
        assert!(
            retrieved_job.is_upstream_job,
            "Job should be marked as upstream"
        );
    }

    #[test]
    fn test_difficulty_100_conversion() {
        let difficulty = 100.5;
        let target_100 = DownstreamClient::target_from_difficulty(difficulty);

        let compact_100 = target_100.to_compact_lossy();
        println!("--- Difficulty 100.0 Test ---");
        println!("Difficulty: {}", difficulty);
        let target_100_hex = hex::encode(target_100.to_be_bytes());
        println!("Target (Hex): {}", target_100_hex);
        println!("Target (nBits): {:#x}", compact_100.to_consensus());

        let expected_prefix = "00000000028c";
        let actual_hex = target_100_hex;

        assert!(
            actual_hex.starts_with(expected_prefix),
            "Target for Diff 100 should start with {}, got {}",
            expected_prefix,
            actual_hex
        );

        println!("Assertion Passed: Target matches expected value for Diff 100.");
    }

    #[tokio::test]
    pub async fn server_start_test() {
        let ibd_or_not: AtomicBool = AtomicBool::new(false);
        let test_ibd_spinlock = Arc::new(ibd_or_not);
        let genesis_beads = Vec::from([]);
        let test_braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(
            genesis_beads,
            PoolNetwork::Cpunet,
        )));
        let connection_mapping = Arc::new(RwLock::new(ConnectionMapping::new()));
        let job_store = Arc::new(Mutex::new(GlobalJobStore::new(
            crate::GLOBAL_JOB_STORE_CAPACITY,
        )));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;
        let (_test_db_handler, test_db_tx) =
            DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let (swarm_handler, mut swarm_command_receiver) =
            SwarmHandler::new(Arc::clone(&test_braid), test_db_tx, DashboardEvents::new());
        let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            ..Default::default()
        };

        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let bound_addr = listener.local_addr().unwrap();
        let addr = bound_addr.to_string();

        let mut server = Server::new(
            config.clone(),
            connection_mapping.clone(),
            None,
            PoolNetwork::Cpunet,
        );

        let server_task = tokio::spawn(async move {
            let _ = server
                .run_stratum_service(
                    listener,
                    job_store,
                    notify_tx,
                    swarm_handler_arc,
                    test_ibd_spinlock.clone(),
                    None,
                    None,
                    None,
                )
                .await;
        });
        let mut mock_connection_handles = Vec::new();
        for i in 0..3 {
            let addr_clone = addr.clone();
            mock_connection_handles.push(tokio::spawn(async move {
                let mut stream = TcpStream::connect(&addr_clone).await.unwrap();
                let msg = format!(
                    r#"{{"id":{},"method":"mining.subscribe","params":[]}}"#,
                    i + 1
                );
                stream.write_all(msg.as_bytes()).await.unwrap();
                stream.write_all(b"\n").await.unwrap();
                stream
            }));
        }

        let streams: Vec<TcpStream> = futures::future::join_all(mock_connection_handles)
            .await
            .into_iter()
            .map(|r| r.unwrap())
            .collect();

        tokio::time::sleep(Duration::from_millis(500)).await;

        let conn_map = connection_mapping.read().await;
        assert_eq!(conn_map.downstream_channel_mapping.len(), 3);
        drop(streams);
        drop(server_task);
    }

    #[tokio::test]
    pub async fn server_subscribe_response() {
        let ibd_or_not: AtomicBool = AtomicBool::new(false);
        let test_ibd_spinlock = Arc::new(ibd_or_not);
        let connection_mapping = Arc::new(RwLock::new(ConnectionMapping::new()));
        let genesis_beads = Vec::from([]);
        let test_braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(
            genesis_beads,
            PoolNetwork::Cpunet,
        )));
        let job_store = Arc::new(Mutex::new(GlobalJobStore::new(
            crate::GLOBAL_JOB_STORE_CAPACITY,
        )));
        let (_test_db_handler, test_db_tx) =
            DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let (swarm_handler, mut swarm_command_receiver) =
            SwarmHandler::new(Arc::clone(&test_braid), test_db_tx, DashboardEvents::new());
        let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;

        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            ..Default::default()
        };

        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let bound_addr = listener.local_addr().unwrap();

        let mut server = Server::new(
            config.clone(),
            connection_mapping.clone(),
            None,
            PoolNetwork::Cpunet,
        );

        let server_task = tokio::spawn(async move {
            let _ = server
                .run_stratum_service(
                    listener,
                    job_store,
                    notify_tx,
                    swarm_handler_arc,
                    test_ibd_spinlock,
                    None,
                    None,
                    None,
                )
                .await;
        });

        let mut stream = TcpStream::connect(bound_addr).await.unwrap();

        let msg = r#"{"id":1,"method":"mining.subscribe","params":[]}"#;
        stream.write_all(msg.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();

        let mut reader = BufReader::new(stream);
        let mut response_line = String::new();
        reader.read_line(&mut response_line).await.unwrap();

        let parsed: serde_json::Value = serde_json::from_str(response_line.trim()).unwrap();
        println!("Parsed response: {:?}", parsed);
    }

    #[tokio::test]
    async fn test_mining_authorize_response() {
        let ibd_or_not: AtomicBool = AtomicBool::new(false);
        let ibd_spinlock = Arc::new(ibd_or_not);
        let connection_mapping = Arc::new(RwLock::new(ConnectionMapping::new()));
        let genesis_beads = Vec::from([]);
        let test_braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(
            genesis_beads,
            PoolNetwork::Cpunet,
        )));
        let job_store = Arc::new(Mutex::new(GlobalJobStore::new(
            crate::GLOBAL_JOB_STORE_CAPACITY,
        )));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;
        let (_test_db_handler, test_db_tx) =
            DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let (swarm_handler, mut swarm_command_receiver) =
            SwarmHandler::new(Arc::clone(&test_braid), test_db_tx, DashboardEvents::new());
        let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            ..Default::default()
        };

        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let bound_addr = listener.local_addr().unwrap();

        let mut server = Server::new(config, connection_mapping, None, PoolNetwork::Cpunet);
        tokio::spawn(async move {
            let _ = server
                .run_stratum_service(
                    listener,
                    job_store,
                    notify_tx,
                    swarm_handler_arc,
                    ibd_spinlock.clone(),
                    None,
                    None,
                    None,
                )
                .await;
        });

        let mut stream = TcpStream::connect(bound_addr).await.unwrap();

        let request = r#"{"id":2,"method":"mining.authorize","params":["satoshi","braidpool"]}"#;
        stream.write_all(request.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();
        let mut reader = BufReader::new(stream);

        let mut line = String::new();
        reader.read_line(&mut line).await.unwrap();
        let response: serde_json::Value = serde_json::from_str(line.trim()).unwrap();

        assert_eq!(response["id"], 2);
        assert!(response["result"].is_boolean());
        assert_eq!(response["result"], true);
    }

    #[tokio::test]
    async fn test_mining_set_difficulty_response() {
        let ibd_or_not: AtomicBool = AtomicBool::new(false);
        let ibd_spinlock = Arc::new(ibd_or_not);
        let connection_mapping = Arc::new(RwLock::new(ConnectionMapping::new()));
        let genesis_beads = Vec::from([]);
        let test_braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(
            genesis_beads,
            PoolNetwork::Cpunet,
        )));
        let (_test_db_handler, test_db_tx) =
            DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let job_store = Arc::new(Mutex::new(GlobalJobStore::new(
            crate::GLOBAL_JOB_STORE_CAPACITY,
        )));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;
        let (swarm_handler, mut swarm_command_receiver) =
            SwarmHandler::new(Arc::clone(&test_braid), test_db_tx, DashboardEvents::new());
        let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            ..Default::default()
        };
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let bound_addr = listener.local_addr().unwrap();

        let mut server = Server::new(config, connection_mapping, None, PoolNetwork::Cpunet);
        tokio::spawn(async move {
            let _ = server
                .run_stratum_service(
                    listener,
                    job_store,
                    notify_tx,
                    swarm_handler_arc,
                    ibd_spinlock.clone(),
                    None,
                    None,
                    None,
                )
                .await;
        });
        let mut stream = TcpStream::connect(bound_addr).await.unwrap();
        let request = r#"{"id":3,"method":"mining.suggest_difficulty","params":[1000]}"#;
        stream.write_all(request.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();
        let mut reader = BufReader::new(stream);
        let mut line = String::new();
        reader.read_line(&mut line).await.unwrap();
        let response: serde_json::Value = serde_json::from_str(line.trim()).unwrap();
        assert_eq!(response["method"], "mining.set_difficulty");
    }

    #[tokio::test]
    async fn test_invalid_json() {
        let ibd_or_not: AtomicBool = AtomicBool::new(false);
        let ibd_spinlock = Arc::new(ibd_or_not);
        let connection_mapping = Arc::new(RwLock::new(ConnectionMapping::new()));
        let genesis_beads = Vec::from([]);
        let test_braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(
            genesis_beads,
            PoolNetwork::Cpunet,
        )));
        let (_test_db_handler, test_db_tx) =
            DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let job_store = Arc::new(Mutex::new(GlobalJobStore::new(
            crate::GLOBAL_JOB_STORE_CAPACITY,
        )));
        let (notify_tx, _notify_rx) = mpsc::channel::<NotifyCmd>(32);
        let (swarm_handler, mut swarm_command_receiver) =
            SwarmHandler::new(Arc::clone(&test_braid), test_db_tx, DashboardEvents::new());
        let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            ..Default::default()
        };

        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let bound_addr = listener.local_addr().unwrap();

        let mut server = Server::new(
            config,
            connection_mapping.clone(),
            None,
            PoolNetwork::Cpunet,
        );
        let job_store_clone = job_store.clone();
        let notify_tx_clone = notify_tx.clone();
        tokio::spawn(async move {
            let _ = server
                .run_stratum_service(
                    listener,
                    job_store_clone,
                    notify_tx_clone,
                    swarm_handler_arc,
                    ibd_spinlock,
                    None,
                    None,
                    None,
                )
                .await;
        });

        let mut stream = TcpStream::connect(bound_addr).await.unwrap();

        stream
            .write_all(b"{\"method\":\"mining.subscribe\", \"params\": [\"test\", 1]\n")
            .await
            .unwrap();
        stream.flush().await.unwrap();

        stream.write_all(b"not a json at all\n").await.unwrap();
        stream.flush().await.unwrap();

        tokio::time::sleep(std::time::Duration::from_millis(200)).await;

        let valid_msg = r#"{"id": 1, "method": "mining.subscribe", "params": []}"#;
        stream
            .write_all(format!("{}\n", valid_msg).as_bytes())
            .await
            .unwrap();
        stream.flush().await.unwrap();

        let mut reader = BufReader::new(stream);
        let mut line = String::new();
        let bytes_read = reader.read_line(&mut line).await.unwrap();
        let response: serde_json::Value = serde_json::from_str(line.trim()).unwrap();
        assert_eq!(response["id"], 1);
    }

    #[tokio::test]
    async fn submit_work_no_version_rolling() {
        use crate::config::PoolNetwork;
        let genesis_beads = Vec::from([]);
        let test_braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(
            genesis_beads,
            PoolNetwork::Cpunet,
        )));
        let (_test_db_handler, test_db_tx) =
            DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let (swarm_handler, mut swarm_command_receiver) =
            SwarmHandler::new(Arc::clone(&test_braid), test_db_tx, DashboardEvents::new());
        let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
        let test_merkle_bytes: [u8; 32] = [0u8; 32];
        let mut test_witness = Witness::new();
        test_witness.push(vec![0u8; 32]);
        let test_coinbase_transaction: Transaction = Transaction {
            version: bitcoin::blockdata::transaction::Version::TWO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::from_hex(
                    "02611e1001010101010101010101010101010101094272616964706f6f6c",
                )
                .unwrap(),
                sequence: Sequence::MAX,
                witness: test_witness.clone(),
            }],
            output: vec![
                TxOut {
                    value: Amount::from_btc(50.0).unwrap(),
                    script_pubkey: ScriptBuf::from_hex(
                        "0014e470d0179325db88b55771f6c0a5139dd81d7318",
                    )
                    .unwrap(),
                },
                TxOut {
                    value: Amount::from_sat(0),
                    script_pubkey: ScriptBuf::from_hex("6a24aa21a9ede2f61c3f71d1defd3fa999dfa36953755c690689799962b48bebd836974e8cf9")
                        .unwrap(),
                },
                TxOut {
                    value: Amount::from_sat(0),
                    script_pubkey: ScriptBuf::from_hex(
                        "6a286272616964706f6f6c5f626561645f6d657461646174615f686173685f3332620102030405060708",
                    )
                    .unwrap(),
                },
            ],
            lock_time: LockTime::ZERO,
        };
        let test_template_header = bitcoin::block::Header {
            bits: bitcoin::pow::CompactTarget::from_unprefixed_hex("207fffff").unwrap(),
            nonce: 0,
            version: BlockVersion::from_consensus(536870912),
            time: 1759477299,
            prev_blockhash: BlockHash::from_str(
                "000000004357ac765395ad29220608af219e3090d75076f160bae2a195b3ebe6",
            )
            .unwrap(),
            merkle_root: TxMerkleNode::from_byte_array(test_merkle_bytes),
        };
        let mut test_template = BlockTemplate {
            version: test_template_header.version,
            previousblockhash: test_template_header.prev_blockhash,
            transactions: vec![test_coinbase_transaction],
            curtime: test_template_header.time,
            bits: test_template_header.bits,
            ..Default::default()
        };
        let mut constructed_test_notification = Notifier::construct_job_notification(
            false,
            test_template.clone(),
            TemplateId::Braidpool(1),
            vec![],
        )
        .await
        .unwrap();
        println!(
            "Constructed test notification: {:?}",
            constructed_test_notification
        );
        let constructed_test_notification_ref = constructed_test_notification.clone();
        let current_system_time = std::time::SystemTime::now();
        let duration_since_epoch = current_system_time.duration_since(UNIX_EPOCH).unwrap();
        let unix_timestamp = duration_since_epoch.as_secs().to_u32().unwrap();
        let mut mock_downstream_handler = DownstreamClient::new(PoolNetwork::Cpunet);
        mock_downstream_handler.authorized = true;
        let mock_global_job_store: Arc<Mutex<GlobalJobStore>> = Arc::new(Mutex::new(
            GlobalJobStore::new(crate::GLOBAL_JOB_STORE_CAPACITY),
        ));
        test_template.transactions.remove(0);
        let job_details = JobDetails {
            blocktemplate: test_template,
            coinbase1: constructed_test_notification_ref.clone().coinbase1.clone(),
            coinbase2: constructed_test_notification_ref.clone().coinbase2.clone(),
            coinbase_merkle_path: vec![],
            coinbase_witness_commitment: Some(test_witness),
            job_sent_time: unix_timestamp,
            is_upstream_job: false,
        };
        let numeric_job_id = mock_global_job_store
            .lock()
            .await
            .insert(TemplateId::Braidpool(1), Arc::new(job_details.clone()));
        let configure_test_request = json!([
            [
                "version-rolling"
            ],
            {
                "version-rolling.mask": "ffffffff"
            }
        ]);
        let test_extranonce_1 = hex::decode("000000009495ac08").unwrap();
        mock_downstream_handler.extranonce1 = test_extranonce_1;
        mock_downstream_handler.network = PoolNetwork::Cpunet;
        let configure_response = mock_downstream_handler
            .handle_configure(&configure_test_request, 1, None)
            .await
            .unwrap();
        match configure_response {
            StratumResponses::StandardResponse { std_response } => {
                let result = std_response.result.unwrap();
                assert_eq!(result["version-rolling"], true);
                assert_eq!(result["version-rolling.mask"], "1fffe000");
            }
            _ => panic!("Expected StandardResponse from mining.configure"),
        }
        assert_eq!(
            mock_downstream_handler.version_rolling_mask.as_deref(),
            Some("1fffe000")
        );

        let extranonce1_hex_for_grind = hex::encode(&mock_downstream_handler.extranonce1);
        let extranonce2_for_grind = "0000000003000000";
        let coinbase_hex_for_grind = format!(
            "{}{}{}{}",
            constructed_test_notification_ref.coinbase1,
            extranonce1_hex_for_grind,
            extranonce2_for_grind,
            constructed_test_notification_ref.coinbase2,
        );
        let coinbase_bytes_for_grind = hex::decode(&coinbase_hex_for_grind).unwrap();
        let mut grind_cursor = Cursor::new(coinbase_bytes_for_grind);
        let coinbase_tx_for_grind =
            bitcoin::Transaction::consensus_decode(&mut grind_cursor).unwrap();
        let merkle_root_bytes_for_grind =
            calculate_merkle_root(coinbase_tx_for_grind.compute_txid(), &[]);
        let merkle_root_for_grind = TxMerkleNode::from_byte_array(merkle_root_bytes_for_grind);
        let grind_bits = bitcoin::pow::CompactTarget::from_unprefixed_hex("207fffff").unwrap();
        let grind_target = bitcoin::Target::from_compact(grind_bits);
        let grind_ntime = u32::from_str_radix("68df7e33", 16).unwrap();
        let mut valid_nonce: u32 = 0;
        for nonce in 0u32..=u32::MAX {
            let grind_header = BlockHeader {
                version: BlockVersion::from_consensus(536870912),
                prev_blockhash: test_template_header.prev_blockhash,
                merkle_root: merkle_root_for_grind,
                time: grind_ntime,
                bits: grind_bits,
                nonce,
            };
            if grind_target.is_met_by(compute_block_hash(&grind_header, PoolNetwork::Cpunet)) {
                valid_nonce = nonce;
                break;
            }
        }
        let valid_nonce_hex = format!("{:08x}", valid_nonce);

        let test_submit_request_params = json!([
            "bitaxe",
            numeric_job_id.to_string(),
            "0000000003000000",
            "68df7e33",
            valid_nonce_hex,
            "00000000"
        ]);
        let submit_response: StratumResponses = mock_downstream_handler
            .handle_submit(
                &test_submit_request_params,
                mock_global_job_store.clone(),
                2,
                swarm_handler_arc,
                None,
                None,
                None,
            )
            .await
            .unwrap();
        match submit_response {
            StratumResponses::StandardResponse { std_response } => {
                let resp = std_response.result.unwrap();
                let json_response = resp.as_bool().unwrap();
                assert_eq!(json_response, true);
            }
            _ => {
                panic!("Expected StandardResponse, got a different response type");
            }
        }

        let mut complete_coinbase = coinbase_tx_for_grind.clone();
        complete_coinbase
            .input
            .get_mut(0)
            .unwrap()
            .witness
            .push(vec![0u8; 32]);
        let complete_block_header = BlockHeader {
            version: BlockVersion::from_consensus(536870912),
            prev_blockhash: test_template_header.prev_blockhash,
            merkle_root: merkle_root_for_grind,
            time: grind_ntime,
            bits: grind_bits,
            nonce: valid_nonce,
        };
        let complete_block = bitcoin::Block {
            header: complete_block_header,
            txdata: vec![complete_coinbase],
        };
        let complete_block_hex = hex::encode(serialize(&complete_block));

        let expected_complete_block_hex = "00000020e6ebb395a1e2ba60f17650d790309e21af08062229ad955376ac57430000000090dea459e4b4db9ed0d542fc9415f04312b9b2fc1c3b07bd7a417b715d948ab4337edf68ffff7f200300000001020000000001010000000000000000000000000000000000000000000000000000000000000000ffffffff1e02611e10000000009495ac080000000003000000094272616964706f6f6cffffffff0300f2052a01000000160014e470d0179325db88b55771f6c0a5139dd81d73180000000000000000266a24aa21a9ede2f61c3f71d1defd3fa999dfa36953755c690689799962b48bebd836974e8cf900000000000000002a6a286272616964706f6f6c5f626561645f6d657461646174615f686173685f33326201020304050607080120000000000000000000000000000000000000000000000000000000000000000000000000";
        assert_eq!(complete_block_hex, expected_complete_block_hex);

        assert!(complete_block_hex.starts_with("00000020"));
        assert!(complete_block_hex
            .contains("e6ebb395a1e2ba60f17650d790309e21af08062229ad955376ac574300000000"));
    }

    /// Minimal job+client setup used by the ntime/nonce fast-fail tests.
    async fn submit_setup() -> (
        DownstreamClient,
        Arc<Mutex<GlobalJobStore>>,
        Arc<Mutex<SwarmHandler>>,
        u64,
    ) {
        let template = BlockTemplate {
            bits: bitcoin::pow::CompactTarget::from_unprefixed_hex("207fffff").unwrap(),
            ..BlockTemplate::default()
        };
        let job_details = Arc::new(JobDetails {
            blocktemplate: template,
            coinbase1: String::new(),
            coinbase2: String::new(),
            coinbase_merkle_path: vec![],
            coinbase_witness_commitment: None,
            job_sent_time: 0,
            is_upstream_job: false,
        });
        let store = Arc::new(Mutex::new(GlobalJobStore::new(
            crate::GLOBAL_JOB_STORE_CAPACITY,
        )));
        let job_id = store
            .lock()
            .await
            .insert(TemplateId::Braidpool(1), job_details);
        let mut client = DownstreamClient::new(PoolNetwork::Cpunet);
        client.authorized = true;
        client.extranonce1 = vec![0u8; 8];
        let test_braid = Arc::new(RwLock::new(braid::Braid::new(vec![], PoolNetwork::Cpunet)));
        let (_db, db_tx) = DBHandler::new_in_memory(PoolNetwork::Cpunet).await.unwrap();
        let (swarm, _rx) = SwarmHandler::new(test_braid, db_tx, DashboardEvents::new());
        let swarm_arc = Arc::new(Mutex::new(swarm));
        (client, store, swarm_arc, job_id)
    }

    #[tokio::test]
    async fn non_hex_ntime_returns_err_before_coinbase_work() {
        let (mut client, map, swarm, job_id) = submit_setup().await;
        let params = json!([
            "miner",
            job_id.to_string(),
            "0000000000000000", // extranonce2
            "zzzzzzzz",         // invalid ntime — not hex
            "00000000",         // nonce
        ]);
        let result = client
            .handle_submit(&params, map, 1, swarm, None, None, None)
            .await;
        assert!(
            matches!(result, Err(crate::error::StratumErrors::InvalidMethodParams { .. })),
            "non-hex ntime must be rejected before coinbase work"
        );
    }

    #[tokio::test]
    async fn unpadded_nonce_not_rejected_by_length_check() {
        // Pins the decision not to enforce strict 8-char width on nonce.
        // A miner using {:x} formatting sends "3" for nonce 3 — correct value, just unpadded.
        // A length check would reject valid shares like this one.
        let (mut client, map, swarm, job_id) = submit_setup().await;
        let params = json!([
            "miner",
            job_id.to_string(),
            "0000000000000000",
            "68df7e33",
            "3", // unpadded nonce, correct value
        ]);
        let result = client
            .handle_submit(&params, map, 1, swarm, None, None, None)
            .await;
        // Passes the parse step; fails later at coinbase decode (InvalidCoinbase),
        // not at nonce parsing (InvalidMethodParams).
        assert!(
            !matches!(result, Err(crate::error::StratumErrors::InvalidMethodParams { .. })),
            "unpadded nonce must not be rejected before coinbase work"
        );
    }

    #[test]
    fn prev_hash_test() {
        let prev_test_hash = "00000000cbdd48c69c45ffd07dc26fc3668bb70870374354535061f8f5304c7c";
        let reversed_hash = reverse_four_byte_chunks(prev_test_hash).unwrap();

        assert_eq!(
            reversed_hash,
            "f5304c7c535061f870374354668bb7087dc26fc39c45ffd0cbdd48c600000000".to_string()
        );
    }

    #[test]
    fn test_merkle_root_construction() {
        let coinbase_string_non_segwit = "02000000010000000000000000000000000000000000000000000000000000000000000000ffffffff170305190408ac53db1b00000000094272616964706f6f6cffffffff03c81d039500000000160014af0ce4a33e61762bde14de428440a9def7acc9310000000000000000266a24aa21a9edac3e72f41e3e7cda29fa3e372e7209108db9c2b2bff9e7b51fdffb10b89a9e4300000000000000002a6a286272616964706f6f6c5f626561645f6d657461646174615f686173685f333262010203040506070800000000";
        let coinbase_bytes = hex::decode(coinbase_string_non_segwit).unwrap();
        let mut cursor = Cursor::new(coinbase_bytes);
        let coinbase_tx = Transaction::consensus_decode(&mut cursor).unwrap();
        let coinbase_wtxid = coinbase_tx.compute_wtxid();
        let coinbase_txid = coinbase_tx.compute_txid();
        assert_eq!(coinbase_txid.to_string(), coinbase_wtxid.to_string());
        let test_merkle_branches = [
            "0ce0d53011438c88cdff30f6312ca67d87bf14fb39e449a5cf90cd369d750e21",
            "562d5094b1362ac66b126a910908eea2a17b06891483ee90447914dcad65c96b",
            "d485ae53320318f499c91e3b8899c004d10ba358aa143ace70aab9f4448aac0e",
            "37aabcd6778b0a07f06c7d9f5f12ca156b679bdf69f1c6327a06d30c0002b49d",
            "408040846f74ad0a82e58a17431b8fde5f62e5e913f34ffe21e29b907eda7e0f",
        ];
        let mut merkle_branches_serialized: Vec<Vec<u8>> = Vec::new();
        for merkle_branch_str in test_merkle_branches {
            let mut merkle_branch_bytes: [u8; 32] = [0u8; 32];
            hex::decode_to_slice(merkle_branch_str, &mut merkle_branch_bytes).unwrap();
            merkle_branches_serialized.push(Vec::from(merkle_branch_bytes));
        }
        println!("Merkle branches bytes - {:?}", merkle_branches_serialized);
        let merkle_root_bytes =
            calculate_merkle_root(coinbase_txid, &merkle_branches_serialized.as_slice());
        let mr = TxMerkleNode::from_byte_array(merkle_root_bytes);
        println!("Merkle root - {:?}", mr.to_string());
        assert_eq!(
            mr.to_string(),
            "690699e45d09d84d81cb58a4f8ba734e7fc90856d8b24524797f9a54ff57b1a1".to_string()
        );
    }

    #[test]
    fn test_unique_extranonce1_per_connection() {
        let client1 = DownstreamClient::new(PoolNetwork::Cpunet);
        let client2 = DownstreamClient::new(PoolNetwork::Cpunet);
        let client3 = DownstreamClient::new(PoolNetwork::Cpunet);

        // connection_ids must be strictly increasing
        assert!(client2.connection_id() > client1.connection_id());
        assert!(client3.connection_id() > client2.connection_id());

        // extranonce1 must be unique across all three connections
        assert_ne!(client1.extranonce1, client2.extranonce1);
        assert_ne!(client2.extranonce1, client3.extranonce1);
        assert_ne!(client1.extranonce1, client3.extranonce1);

        // extranonce1 must be exactly EXTRANONCE1_SIZE bytes
        assert_eq!(client1.extranonce1.len(), UPSTREAM_EXTRANONCE1_SIZE);
        assert_eq!(client2.extranonce1.len(), UPSTREAM_EXTRANONCE1_SIZE);
        assert_eq!(client3.extranonce1.len(), UPSTREAM_EXTRANONCE1_SIZE);
    }
}

#[cfg(test)]
mod global_job_store_tests {
    use std::sync::Arc;
    use crate::TemplateId;
    use super::*;

    fn dummy_job() -> Arc<JobDetails> {
        Arc::new(JobDetails {
            blocktemplate: BlockTemplate::default(),
            coinbase1: String::new(),
            coinbase2: String::new(),
            coinbase_merkle_path: vec![],
            coinbase_witness_commitment: None,
            job_sent_time: 0,
            is_upstream_job: false,
        })
    }

    #[test]
    fn eviction_at_capacity() {
        let mut store = GlobalJobStore::new(3);
        let j0 = store.insert(TemplateId::Braidpool(1), dummy_job());
        let j1 = store.insert(TemplateId::Braidpool(2), dummy_job());
        let j2 = store.insert(TemplateId::Braidpool(3), dummy_job());
        // Fourth insert evicts j0; template 1 has no other references so it is freed.
        let j3 = store.insert(TemplateId::Braidpool(4), dummy_job());
        assert!(
            store.get_by_job_id(j0).is_err(),
            "evicted job_id should not resolve"
        );
        assert!(store.get_by_job_id(j1).is_ok());
        assert!(store.get_by_job_id(j2).is_ok());
        assert!(store.get_by_job_id(j3).is_ok());
    }

    #[test]
    fn still_referenced_template_survives_eviction() {
        let mut store = GlobalJobStore::new(3);
        // Two job_ids pointing at the same template_id.
        let j0 = store.insert(TemplateId::Braidpool(1), dummy_job()); // job_id 0 → template 1
        let j1 = store.insert(TemplateId::Braidpool(1), dummy_job()); // job_id 1 → template 1 (Arc reused)
        let j2 = store.insert(TemplateId::Braidpool(2), dummy_job()); // job_id 2 → template 2
                                                                      // Fourth insert evicts j0; template 1 is still referenced by j1, so it stays.
        let j3 = store.insert(TemplateId::Braidpool(3), dummy_job());
        assert!(
            store.get_by_job_id(j0).is_err(),
            "evicted job_id should not resolve"
        );
        assert!(
            store.get_by_job_id(j1).is_ok(),
            "template referenced by j1 must survive"
        );
        assert!(store.get_by_job_id(j2).is_ok());
        assert!(store.get_by_job_id(j3).is_ok());
    }

    #[test]
    fn arc_reuse_on_duplicate_template_id() {
        let mut store = GlobalJobStore::new(5);
        let original = dummy_job();
        let j0 = store.insert(TemplateId::Braidpool(1), Arc::clone(&original));
        let j1 = store.insert(TemplateId::Braidpool(1), dummy_job()); // same template_id, different Arc offered
        let job0 = store.get_by_job_id(j0).unwrap();
        let job1 = store.get_by_job_id(j1).unwrap();
        assert!(
            Arc::ptr_eq(&job0, &job1),
            "both job_ids must point to the same Arc allocation"
        );
    }

    #[test]
    fn evicted_id_returns_not_found() {
        let mut store = GlobalJobStore::new(1);
        let j0 = store.insert(TemplateId::Braidpool(1), dummy_job());
        let _j1 = store.insert(TemplateId::Braidpool(2), dummy_job()); // evicts j0
        assert!(store.get_by_job_id(j0).is_err());
    }

    #[test]
    fn latest_job_id_for_returns_max_id() {
        let mut store = GlobalJobStore::new(10);
        store.insert(TemplateId::Braidpool(1), dummy_job()); // job_id 0
        store.insert(TemplateId::Braidpool(1), dummy_job()); // job_id 1
        store.insert(TemplateId::Braidpool(1), dummy_job()); // job_id 2
        assert_eq!(store.latest_job_id_for(&TemplateId::Braidpool(1)), Some(2));
        assert_eq!(store.latest_job_id_for(&TemplateId::Braidpool(99)), None);
    }

    #[test]
    fn latest_job_id_for_absent_after_eviction() {
        let mut store = GlobalJobStore::new(2);
        store.insert(TemplateId::Braidpool(1), dummy_job()); // job_id 0 → template 1
        store.insert(TemplateId::Braidpool(2), dummy_job()); // job_id 1 → template 2
        store.insert(TemplateId::Braidpool(3), dummy_job()); // job_id 2 → template 3; evicts j0, template 1 freed
                                                             // Template 1 has no remaining job_id, so latest_job_id_for returns None.
        assert_eq!(store.latest_job_id_for(&TemplateId::Braidpool(1)), None);
        assert_eq!(store.latest_job_id_for(&TemplateId::Braidpool(2)), Some(1));
    }
}
