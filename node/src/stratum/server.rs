use std::{net::SocketAddr, sync::Arc};
use std::sync::atomic::{AtomicBool, Ordering};
use std::collections::VecDeque;

use futures::{FutureExt, lock::Mutex};
use rand::RngCore;
use serde_json::Value;
use tokio::{
    io::{AsyncWriteExt, BufReader},
    net::{
        tcp::{OwnedReadHalf, OwnedWriteHalf},
        TcpListener,
    },
    sync::{mpsc, RwLock},
};
use tokio_stream::StreamExt;
use tokio_util::codec::{FramedRead, LinesCodec};
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

use crate::config::PoolNetwork;
use crate::error::StratumErrors;
use crate::{SwarmHandler, EXTRANONCE2_SIZE};

use super::client::DownstreamClient;
use super::connection::{ConnectionMapping, ControlMsg};
use super::job_store::GlobalJobStore;
use super::notifier::NotifyCmd;
use super::types::{BlockSubmissionRequest, StratumServerConfig, StandardRequest};
use super::DISCONNECT_SIGNAL;

/// Stratum server: manages configuration and all downstream miner connections.
///
/// `downstream_connection_mapping` is wrapped in `Arc<RwLock<...>>` to allow concurrent
/// reads from the RPC and Notifier while stratum holds a write lock only for add/remove.
#[derive(Debug)]
pub struct Server {
    stratum_config: StratumServerConfig,
    downstream_connection_mapping: Arc<RwLock<ConnectionMapping>>,
    block_submission_tx: Option<mpsc::UnboundedSender<BlockSubmissionRequest>>,
    network: PoolNetwork,
}

impl Server {
    pub fn new(
        server_config: StratumServerConfig,
        connection_mapping_arc: Arc<RwLock<ConnectionMapping>>,
        block_submission_tx: Option<mpsc::UnboundedSender<BlockSubmissionRequest>>,
        network: PoolNetwork,
    ) -> Self {
        debug!(config = ?server_config, network = %network, "Initializing stratum server");

        Self {
            stratum_config: server_config,
            downstream_connection_mapping: connection_mapping_arc,
            block_submission_tx,
            network,
        }
    }

    /// Starts the Stratum server and accepts incoming miner connections.
    ///
    /// Runs indefinitely. Returns only on listener error or unrecoverable failure.
    pub async fn run_stratum_service(
        &mut self,
        listener: TcpListener,
        global_job_store: Arc<Mutex<GlobalJobStore>>,
        notification_sender: mpsc::Sender<NotifyCmd>,
        swarm_handler: Arc<Mutex<SwarmHandler>>,
        ibd_or_not: Arc<AtomicBool>,
        audit_dag: Option<Arc<Mutex<crate::audit::AuditDAG>>>,
        upstream_share_tx: Option<mpsc::Sender<crate::upstream_pool::UpstreamShare>>,
        upstream_configure_tx: Option<mpsc::Sender<(Value, u64, mpsc::Sender<Value>)>>,
    ) -> Result<(), Box<std::io::Error>> {
        debug!("Starting stratum server");
        let bound_addr = listener.local_addr()?;
        let endpoints = crate::utils::server_endpoints(
            &self.stratum_config.hostname,
            bound_addr.port(),
            "stratum+tcp",
        );
        if endpoints.is_empty() {
            warn!(
                host = %self.stratum_config.hostname,
                port = %bound_addr.port(),
                "Server listening but no interfaces were discovered"
            );
        } else {
            for endpoint in endpoints {
                info!(endpoint = %endpoint, "Stratum server is listening");
            }
        }
        loop {
            tokio::select! {
                event = listener.accept() => {
                    if ibd_or_not.load(Ordering::SeqCst) == true {
                        warn!("Braid node not synced and is under IBD,skipping the connection from downstream.");
                        continue;
                    }
                    let self_ = Arc::new(Mutex::new(DownstreamClient::new(self.network)));
                    let (connection_id, connection_id_hex) = {
                        let mut client = self_.lock().await;
                        if let Some(ref submission_tx) = self.block_submission_tx {
                            client.block_submission_tx = Some(submission_tx.clone());
                        }
                        let id = client.connection_id();
                        (id, format!("{:x}", id))
                    };
                    match event {
                        Ok((stream, peer_addr)) => {
                            let (reader, writer) = stream.into_split();

                            let (assigned_extranonce1, assigned_extranonce2_size, extranonce2_prefix, is_proxy) = {
                                let mut mapping = self.downstream_connection_mapping.write().await;

                                if self.stratum_config.audit_mode {
                                    let upstream_ext1_clone = mapping.upstream_extranonce1.clone();
                                    let upstream_ext2_size = mapping.upstream_extranonce2_size;

                                    if let (Some(upstream_ext1), Some(_ext2_size)) =
                                        (upstream_ext1_clone, upstream_ext2_size)
                                    {
                                        info!("New audit mode connection using upstream extranonce: {}", upstream_ext1);

                                        let (prefix_bytes, _miner_ext2_size) = mapping.allocate_extranonce2_prefix();
                                        let prefix_u16 = u16::from_be_bytes([prefix_bytes[0], prefix_bytes[1]]);
                                        mapping.register_prefix(peer_addr.to_string(), prefix_u16);

                                        let upstream_ext1_bytes = match hex::decode(&upstream_ext1) {
                                            Ok(bytes) => bytes,
                                            Err(e) => {
                                                error!("Failed to decode upstream extranonce: {}", e);
                                                continue;
                                            }
                                        };

                                        let upstream_ext1_len = upstream_ext1_bytes.len();
                                        let mut extended_extranonce1 = upstream_ext1_bytes;
                                        extended_extranonce1.extend_from_slice(&prefix_bytes);
                                        let bead_hash_commitment = mapping.get_current_bead_commitment();
                                        extended_extranonce1.extend_from_slice(&bead_hash_commitment);
                                        let upstream_ext2_size = mapping.upstream_extranonce2_size.unwrap_or(8);
                                        let miner_ext2_size = upstream_ext2_size
                                            .saturating_sub(prefix_bytes.len())
                                            .saturating_sub(bead_hash_commitment.len());

                                        if miner_ext2_size < 1 {
                                            error!(
                                                "Insufficient extranonce space! Upstream: {}, Prefix: {}, Commitment: {}",
                                                upstream_ext2_size,
                                                prefix_bytes.len(),
                                                bead_hash_commitment.len()
                                            );
                                            continue;
                                        }

                                        if let Some(ref dag) = audit_dag {
                                            info!(
                                                "Registering miner {} with prefix {} and commitment {} in AuditDAG",
                                                peer_addr,
                                                hex::encode(&prefix_bytes),
                                                hex::encode(&bead_hash_commitment)
                                            );
                                            {
                                                let mut dag_guard = dag.lock().await;
                                                dag_guard.register_miner(peer_addr.to_string(), prefix_bytes.clone(), upstream_ext1_len, miner_ext2_size);
                                                if let Some(miner_state) = dag_guard.miner_states.get_mut(&peer_addr.to_string()) {
                                                    let commitment = crate::audit::AuditCommitment::from_hash_prefix(&bead_hash_commitment);
                                                    miner_state.current_commitment = commitment;
                                                    miner_state.previous_commitment = None;
                                                    miner_state.commitment_pending = false;
                                                } else {
                                                    error!(peer = %peer_addr, "Failed to initialize AuditDAG state for miner. Rejecting.");
                                                    continue;
                                                }
                                            }
                                        }

                                        let stats = mapping.get_prefix_stats();
                                        debug!(
                                            audit_mode = true,
                                            peer = %peer_addr,
                                            upstream_extranonce1 = %upstream_ext1,
                                            assigned_prefix = %hex::encode(&prefix_bytes),
                                            full_extranonce1 = %hex::encode(&extended_extranonce1),
                                            miner_extranonce2_size_bytes = %miner_ext2_size,
                                            assigned_prefixes_count = %stats.total_assigned,
                                            available_prefixes_count = %stats.available_for_reuse,
                                            prefix_utilization_percent = %format!("{:.2}%", stats.utilization_percentage()),
                                            "New audit-mode miner: extranonce1 extended with unique prefix; assigned {}-byte rollable extranonce2",
                                            miner_ext2_size
                                        );

                                        (extended_extranonce1, miner_ext2_size, Some(prefix_bytes), true)
                                    } else {
                                        error!("Miner {} tried to connect in audit mode, but upstream pool is not ready yet", peer_addr);
                                        error!("Rejecting connection to prevent mining on wrong chain");
                                        continue;
                                    }
                                } else {
                                    let mut bytes = [0u8; 8];
                                    rand::thread_rng().fill_bytes(&mut bytes);
                                    info!("New Braidpool connection using local extranonce: {}", hex::encode(&bytes));
                                    (bytes.to_vec(), EXTRANONCE2_SIZE, None, false)
                                }
                            };

                            let downstream_client = Arc::new(Mutex::new(DownstreamClient {
                                authorized: false,
                                downstream_ip: peer_addr.to_string(),
                                subscribed: false,
                                suggest_difficulty_done: false,
                                channel_configured: false,
                                connection_id,
                                extranonce1: assigned_extranonce1,
                                extranonce_history: VecDeque::new(),
                                version_rolling_mask: None,
                                version_rolling_min_bit: None,
                                extranonce2_len: assigned_extranonce2_size,
                                extranonce2_prefix: extranonce2_prefix,
                                miner_extranonce2_size: assigned_extranonce2_size,
                                monitor_target: None,
                                block_submission_tx: self.block_submission_tx.clone(),
                                is_proxy_mode: is_proxy,
                                payout_address: None,
                                audit_miner_difficulty: self.stratum_config.audit_miner_difficulty,
                                network: self.network,
                            }));

                            let notification_sender = notification_sender.clone();
                            let swarm_handler_arc_ref = Arc::clone(&swarm_handler);
                            let (downstream_tx, mut downstream_rx) = mpsc::channel(1024);
                            let (control_tx, control_rx) = mpsc::channel(10);
                            self.downstream_connection_mapping
                                .write()
                                .await
                                .new_connection(peer_addr.to_string(), connection_id, downstream_tx.clone(), control_tx);
                            info!(
                                connection_id = %connection_id_hex,
                                peer = %peer_addr,
                                "Miner connected"
                            );
                            self_.lock().await.downstream_ip = peer_addr.to_string();

                            let connection_mapping_clone = Arc::clone(&self.downstream_connection_mapping);
                            let global_job_store_clone = Arc::clone(&global_job_store);
                            let peer_addr_string = peer_addr.to_string();

                            let connection_mapping_for_cleanup = Arc::clone(&self.downstream_connection_mapping);
                            let audit_dag_clone = audit_dag.clone();
                            let upstream_share_tx_clone = upstream_share_tx.clone();
                            let upstream_configure_tx_clone = upstream_configure_tx.clone();

                            tokio::spawn(async move {
                                let _ = Self::handle_connection(
                                    downstream_client.clone(),
                                    peer_addr,
                                    reader,
                                    writer,
                                    &mut downstream_rx,
                                    global_job_store_clone,
                                    downstream_tx,
                                    notification_sender,
                                    swarm_handler_arc_ref,
                                    audit_dag_clone,
                                    upstream_share_tx_clone,
                                    connection_mapping_clone,
                                    upstream_configure_tx_clone,
                                    control_rx,
                                )
                                .await;
                                debug!(
                                    connection_id = %connection_id_hex,
                                    peer = %peer_addr_string,
                                    "Cleaning up disconnected miner"
                                );

                                connection_mapping_for_cleanup
                                    .write()
                                    .await
                                    .remove_peer(&peer_addr_string);

                                debug!(
                                    connection_id = %connection_id_hex,
                                    peer = %peer_addr_string,
                                    "Miner cleanup complete"
                                );
                            });
                        }
                        Err(error) => {
                            info!(
                                connection_id = %connection_id_hex,
                                error = ?error,
                                "Connection failed"
                            );
                        }
                    }
                }
            }
        }
    }

    /// Handles a single downstream miner connection.
    ///
    /// Concurrently reads miner requests and writes server messages via `tokio::select!`.
    pub async fn handle_connection(
        downstream_client: Arc<Mutex<DownstreamClient>>,
        peer_addr: SocketAddr,
        stream_reader: OwnedReadHalf,
        mut stream_writer: OwnedWriteHalf,
        downstream_receiver: &mut mpsc::Receiver<String>,
        global_job_store: Arc<Mutex<GlobalJobStore>>,
        downstream_message_sender: mpsc::Sender<String>,
        notification_sender: mpsc::Sender<NotifyCmd>,
        swarm_handler: Arc<Mutex<SwarmHandler>>,
        audit_dag: Option<Arc<Mutex<crate::audit::AuditDAG>>>,
        upstream_share_tx: Option<mpsc::Sender<crate::upstream_pool::UpstreamShare>>,
        connection_mapping: Arc<RwLock<ConnectionMapping>>,
        upstream_configure_tx: Option<mpsc::Sender<(Value, u64, mpsc::Sender<Value>)>>,
        mut control_rx: mpsc::Receiver<ControlMsg>,
    ) -> Result<(), Box<StratumErrors>> {
        const MAX_LINE_LENGTH: usize = 2_usize.pow(16);
        let reader = BufReader::new(stream_reader);
        let mut framed = FramedRead::new(reader, LinesCodec::new_with_max_length(MAX_LINE_LENGTH));
        let connection_id_hex = {
            let client = downstream_client.lock().await;
            format!("{:x}", client.connection_id())
        };
        debug!(
            connection_id = %connection_id_hex,
            peer = %peer_addr,
            "Handling new connection"
        );

        loop {
            tokio::select! {
                msg_option = downstream_receiver.recv() => {
                    match msg_option {
                        Some(message) => {
                            if message == DISCONNECT_SIGNAL {
                                info!(peer = %peer_addr, "Received explicit disconnect signal");
                                break;
                            }
                            debug!("Sending to {}: {}", peer_addr, message);
                            if let Err(e) = tokio::time::timeout(
                                std::time::Duration::from_secs(5),
                                stream_writer.write_all(format!("{}\n", message).as_bytes())
                            ).await {
                                error!("Write error to {}: {}", peer_addr, e);
                                break;
                            }
                        }
                        None => {
                            info!(peer = %peer_addr, "Channel closed by main, disconnecting miner");
                            break;
                        }
                    }
                }
                ctrl_msg = control_rx.recv() => {
                    match ctrl_msg {
                        Some(ControlMsg::UpdateExtranonce(new_bytes)) => {
                            let mut client = downstream_client.lock().await;
                            let old_extranonce = client.extranonce1.clone();
                            client.extranonce_history.push_front(old_extranonce);
                            if client.extranonce_history.len() > super::COMMITMENT_HISTORY_SIZE {
                                client.extranonce_history.pop_back();
                            }
                            client.extranonce1 = new_bytes;
                            debug!("Internal state updated, extranonce1 changed via control msg");
                        }
                        None => {}
                    }
                }

                line = framed.next().fuse() => {
                    match line {
                        Some(Ok(line)) => {
                            if line.is_empty() {
                                continue;
                            }
                            trace!(
                                connection_id = %connection_id_hex,
                                line = %line,
                                peer = %peer_addr,
                                "Read line from miner"
                            );
                            match serde_json::from_str::<StandardRequest>(&line) {
                                Ok(request) => {
                                    let server_request_res = downstream_client.lock().await
                                        .handle_client_to_server_request(
                                            request,
                                            global_job_store.clone(),
                                            downstream_message_sender.clone(),
                                            notification_sender.clone(),
                                            peer_addr.to_string(),
                                            swarm_handler.clone(),
                                            audit_dag.clone(),
                                            upstream_share_tx.clone(),
                                            connection_mapping.clone(),
                                            upstream_configure_tx.clone(),
                                        )
                                        .await;

                                    if let Err(error) = server_request_res {
                                        error!("Error handling request from {}: {:?}", peer_addr, error);
                                        let error_response = serde_json::json!({
                                            "id": line.parse::<serde_json::Value>()
                                                .ok()
                                                .and_then(|v| v.get("id").cloned())
                                                .unwrap_or(serde_json::json!(null)),
                                            "result": null,
                                            "error": format!("{:?}", error)
                                        });

                                        if let Err(e) = downstream_message_sender
                                            .send(error_response.to_string())
                                            .await
                                        {
                                            error!("Failed to send error response: {}", e);
                                            break;
                                        }
                                    }
                                }
                                Err(e) => {
                                    error!(
                                        connection_id = %connection_id_hex,
                                        peer = %peer_addr,
                                        error = %e,
                                        line = %line,
                                        error_type = "json_parse",
                                        "Failed to parse JSON request"
                                    );
                                }
                            }
                        }
                        Some(Err(e)) => {
                            error!(
                                connection_id = %connection_id_hex,
                                error = %e,
                                peer = %peer_addr,
                                fatal = true,
                                "Fatal error reading from stream"
                            );
                            return Err(Box::new(StratumErrors::UnableToReadStream { error: e }));
                        }
                        None => {
                            info!(
                                connection_id = %connection_id_hex,
                                peer = %peer_addr,
                                "Connection closed by client"
                            );
                            break;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
