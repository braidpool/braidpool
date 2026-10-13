use std::{sync::Arc, time::UNIX_EPOCH};

use bitcoin::hashes::Hash as _;
use futures::lock::Mutex;
use num::ToPrimitive;
use serde_json::json;
use tokio::sync::{mpsc, RwLock};
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

use crate::error::StratumErrors;
use crate::TemplateId;

use super::connection::ConnectionMapping;
use super::job_store::GlobalJobStore;
use super::types::{
    BlockTemplate, JobDetails, JobNotification, JobNotificationResponse,
};

/// Commands sent to the `Notifier` task.
///
/// `SendToAll` broadcasts the most recently received job to all downstream nodes.
/// `SendLatestTemplateToNewDownstream` sends the latest available template to a
/// newly connected node so it can start working immediately.
pub enum NotifyCmd {
    SendToAll {
        template: BlockTemplate,
        merkle_branch_coinbase: Vec<Vec<u8>>,
        template_id: TemplateId,
    },
    SendLatestTemplateToNewDownstream {
        new_downstream_addr: String,
    },
    SendUpstreamJob {
        job_notification: JobNotification,
    },
    BroadcastDifficulty {
        difficulty: f64,
    },
    UpdateExtranonce {
        new_bead_hash: bitcoin::BlockHash,
    },
}

/// `Notifier` that notifies downstream nodes with the latest available jobs via `mining.notify`.
pub struct Notifier {
    notification_receiver: mpsc::Receiver<NotifyCmd>,
    pub job_store: Arc<Mutex<GlobalJobStore>>,
}

fn _to_little_endian(hex_str: &str) -> String {
    hex_str
        .as_bytes()
        .chunks(2)
        .filter_map(|chunk| std::str::from_utf8(chunk).ok())
        .rev()
        .collect::<Vec<&str>>()
        .join("")
}

pub fn reverse_four_byte_chunks(hash_hex: &str) -> Result<String, StratumErrors> {
    if hash_hex.len() != 64 {
        return Err(StratumErrors::PrevHashNotReversed {
            error: "Hash length is incorrect".to_string(),
        });
    }
    let bytes = hex::decode(hash_hex).map_err(|e| StratumErrors::PrevHashNotReversed {
        error: format!("Failed to decode hash hex: {}", e),
    })?;
    let mut reversed_bytes = Vec::with_capacity(bytes.len());
    for chunk in bytes.chunks(4).rev() {
        reversed_bytes.extend_from_slice(chunk);
    }
    Ok(hex::encode(reversed_bytes))
}

impl Notifier {
    pub fn new(
        notification_rx: mpsc::Receiver<NotifyCmd>,
        job_store: Arc<Mutex<GlobalJobStore>>,
    ) -> Self {
        Self {
            notification_receiver: notification_rx,
            job_store,
        }
    }

    pub async fn construct_job_notification(
        clean_job: bool,
        mut notified_template: BlockTemplate,
        template_id: TemplateId,
        merkle_coinbase_branch: Vec<Vec<u8>>,
    ) -> Result<JobNotification, StratumErrors> {
        use bitcoin::consensus::serialize;
        use crate::{EXTRANONCE1_SIZE, EXTRANONCE2_SIZE, EXTRANONCE_SEPARATOR};

        debug!(
            template_id = %template_id,
            clean_job = %clean_job,
            "Constructing JobNotification"
        );

        let coinbase_transaction = match notified_template.transactions.get_mut(0) {
            Some(tx) => tx,
            None => {
                error!(template_id = %template_id, "Template missing coinbase transaction");
                return Err(StratumErrors::JobNotificationNotConstructed {
                    job_template: notified_template,
                });
            }
        };
        let coinbase_witness_commitment = match coinbase_transaction.input.get(0) {
            Some(input) => input.witness.clone(),
            None => {
                error!(template_id = %template_id, "Coinbase transaction has no inputs");
                return Err(StratumErrors::InvalidCoinbase);
            }
        };
        if let Some(input) = coinbase_transaction.input.get_mut(0) {
            input.witness.clear();
        };
        let deserialized_coinbase = serialize::<bitcoin::Transaction>(&coinbase_transaction);
        debug!(
            template_id = %template_id,
            coinbase = ?coinbase_transaction,
            "Deserialized coinbase"
        );

        let separator_pos = match deserialized_coinbase
            .as_slice()
            .windows(EXTRANONCE1_SIZE + EXTRANONCE2_SIZE)
            .position(|window| window == EXTRANONCE_SEPARATOR)
        {
            Some(pos) => pos,
            None => return Err(StratumErrors::InvalidCoinbase),
        };
        let coinbase_1 = hex::encode(&deserialized_coinbase[..separator_pos]);
        let coinbase_2 = hex::encode(
            &deserialized_coinbase[separator_pos + (EXTRANONCE1_SIZE + EXTRANONCE2_SIZE)..],
        );
        debug!(prefix_len = %coinbase_1.len(), suffix_len = %coinbase_2.len(), "Split coinbase transaction");

        let mut merkle_branches: Vec<String> = Vec::new();
        if merkle_coinbase_branch.len() != 0 {
            for sibling_node in merkle_coinbase_branch.iter() {
                let sibling_hex = hex::encode(sibling_node);
                merkle_branches.push(sibling_hex);
            }
        }
        debug!(
            template_id = %template_id,
            merkle_branches = ?merkle_branches,
            "Merkle branches are"
        );

        let prev_block_hash = notified_template.previousblockhash.to_string();
        let prev_block_hash_little_endian =
            match reverse_four_byte_chunks(prev_block_hash.as_str()) {
                Ok(reversed_hash) => reversed_hash,
                Err(error) => {
                    return Err(error);
                }
            };
        let bitcoin_block_version = notified_template.version.to_consensus();
        let bits = notified_template.bits;
        let time = notified_template.curtime;

        Ok(JobNotification {
            job_id: template_id.to_string(),
            prevhash: prev_block_hash_little_endian,
            coinbase1: coinbase_1,
            coinbase2: coinbase_2,
            merkle_branches,
            version: hex::encode(bitcoin_block_version.to_be_bytes()),
            nbits: format!("{:08x}", bits.to_consensus()),
            ntime: hex::encode(time.to_be_bytes()),
            clean_jobs: clean_job,
            coinbase_witness_commitment: Some(coinbase_witness_commitment),
            parsed_bits: None,
        })
    }

    async fn send_upstream_job_notification_to_miner(
        peer_addr: &str,
        connection_entry: &super::connection::ConnectionInfo,
        job_notification: &JobNotification,
        job_store: &Arc<Mutex<GlobalJobStore>>,
    ) -> Result<(), StratumErrors> {
        let mut job_store_guard = job_store.lock().await;
        let compact_bits = match job_notification.parsed_bits {
            Some(bits) => bits,
            None => {
                error!(
                    peer = %peer_addr,
                    job_id = %job_notification.job_id,
                    "Upstream job missing parsed_bits, attempting hex parse"
                );
                bitcoin::CompactTarget::from_hex(&job_notification.nbits).map_err(|e| {
                    StratumErrors::InvalidMethodParams {
                        method: format!("Invalid nbits in upstream job: {}", e),
                    }
                })?
            }
        };
        let mut template = BlockTemplate::default();
        template.bits = compact_bits;
        let version_u32 = u32::from_str_radix(&job_notification.version, 16).map_err(|e| {
            StratumErrors::InvalidMethodParams {
                method: format!("Invalid version hex: {}", e),
            }
        })?;
        template.version = bitcoin::block::Version::from_consensus(version_u32 as i32);
        match hex::decode(&job_notification.prevhash) {
            Ok(bytes) => {
                if bytes.len() == 32 {
                    let mut hash_bytes = [0u8; 32];
                    hash_bytes.copy_from_slice(&bytes);
                    template.previousblockhash = bitcoin::BlockHash::from_byte_array(hash_bytes);
                } else {
                    return Err(StratumErrors::InvalidMethodParams {
                        method: format!("Invalid prevhash length: {}", bytes.len()),
                    });
                }
            }
            Err(e) => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: format!("Failed to decode prevhash: {}", e),
                });
            }
        }
        let unix_timestamp = u32::from_str_radix(&job_notification.ntime, 16).unwrap_or_else(|e| {
            warn!(
                peer = %peer_addr,
                ntime = %job_notification.ntime,
                error = %e,
                "Failed to parse ntime from upstream job, using current time as fallback"
            );
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as u32)
                .unwrap_or(0)
        });
        template.curtime = unix_timestamp;
        let template_id = TemplateId::from_upstream_string(&job_notification.job_id);
        if job_store_guard.get_by_template_id(&template_id).is_err() {
            let job_details = JobDetails {
                blocktemplate: template,
                coinbase1: job_notification.coinbase1.clone(),
                coinbase2: job_notification.coinbase2.clone(),
                coinbase_merkle_path: job_notification.merkle_branches.clone(),
                coinbase_witness_commitment: job_notification.coinbase_witness_commitment.clone(),
                job_sent_time: unix_timestamp,
                is_upstream_job: true,
            };
            job_store_guard.insert(template_id, Arc::new(job_details));
        }
        let upstream_job_id = &job_notification.job_id;
        let job_notification_response = serde_json::json!({
            "method": "mining.notify",
            "params": [
                upstream_job_id,
                job_notification.prevhash,
                job_notification.coinbase1,
                job_notification.coinbase2,
                job_notification.merkle_branches,
                job_notification.version,
                job_notification.nbits,
                job_notification.ntime,
                job_notification.clean_jobs
            ]
        });
        let json_str = serde_json::to_string(&job_notification_response).map_err(|e| {
            StratumErrors::InvalidMethodParams {
                method: format!("Failed to serialize job notification: {}", e),
            }
        })?;
        connection_entry
            .sender
            .send(json_str.clone())
            .await
            .map_err(|e| StratumErrors::NotifyMessageNotSent {
                error: format!("Failed to send upstream job to {}: {}", peer_addr, e),
                msg: json_str,
                msg_type: "UpstreamJob".to_string(),
            })?;
        info!(
            "Sent upstream job {} to {} (bits: {})",
            upstream_job_id, peer_addr, job_notification.nbits
        );
        Ok(())
    }

    fn build_local_job_details(
        template: &BlockTemplate,
        notification: &JobNotification,
        unix_timestamp: u32,
    ) -> Arc<JobDetails> {
        let mut t = template.clone();
        t.transactions.remove(0);
        Arc::new(JobDetails {
            blocktemplate: t,
            coinbase1: notification.coinbase1.clone(),
            coinbase2: notification.coinbase2.clone(),
            coinbase_merkle_path: notification.merkle_branches.clone(),
            coinbase_witness_commitment: notification.coinbase_witness_commitment.clone(),
            job_sent_time: unix_timestamp,
            is_upstream_job: false,
        })
    }

    /// Broadcasts mining jobs to downstream miners.
    ///
    /// Handles two commands: new template → broadcast to all connected miners;
    /// miner reconnect → send current template to the reconnecting miner only.
    pub async fn run_notifier(
        &mut self,
        downstream_connection_map: Arc<RwLock<ConnectionMapping>>,
        latest_template_arc: &mut Arc<Mutex<BlockTemplate>>,
        latest_template_merkle_branch_arc: &mut Arc<Mutex<Vec<Vec<u8>>>>,
        latest_template_id: Arc<Mutex<TemplateId>>,
        upstream_cache: Option<Arc<tokio::sync::RwLock<crate::upstream_pool::UpstreamCache>>>,
        audit_dag: Option<Arc<Mutex<crate::audit::AuditDAG>>>,
    ) -> Result<(), StratumErrors> {
        debug!("Stratum notifier task started");
        while let Some(notification_command) = self.notification_receiver.recv().await {
            match notification_command {
                NotifyCmd::SendToAll {
                    template,
                    merkle_branch_coinbase,
                    template_id,
                } => {
                    debug!(
                        template_id = %template_id,
                        "Received new block template"
                    );
                    let connection_snapshot = downstream_connection_map
                        .read()
                        .await
                        .downstream_channel_mapping
                        .clone();

                    if connection_snapshot.is_empty() {
                        debug!("No miners connected, skipping job notification");
                        continue;
                    }

                    let clean_job = false;
                    let job_notification = match Self::construct_job_notification(
                        clean_job,
                        template.clone(),
                        template_id.clone(),
                        merkle_branch_coinbase.clone(),
                    )
                    .await
                    {
                        Ok(job) => job,
                        Err(e) => {
                            error!(
                                template_id = %template_id,
                                error = %e,
                                "Failed to construct job notification"
                            );
                            continue;
                        }
                    };

                    let unix_timestamp = {
                        let current_system_time = std::time::SystemTime::now();
                        match current_system_time.duration_since(UNIX_EPOCH) {
                            Ok(duration) => match duration.as_secs().to_u32() {
                                Some(ts) => ts,
                                None => {
                                    error!("System timestamp overflow");
                                    continue;
                                }
                            },
                            Err(error) => {
                                return Err(StratumErrors::ErrorFetchingCurrentUNIXTimestamp {
                                    error: error.to_string(),
                                })
                            }
                        }
                    };

                    let job_details =
                        Self::build_local_job_details(&template, &job_notification, unix_timestamp);

                    let numeric_job_id =
                        self.job_store.lock().await.insert(template_id, job_details);

                    for (peer_adr, connection_info) in &connection_snapshot {
                        let connection_id_hex = format!("{:x}", connection_info.connection_id);
                        let job_notification = job_notification.clone();
                        let job_notification_response = JobNotificationResponse {
                            method: "mining.notify".to_string(),
                            params: json!([
                                numeric_job_id.to_string(),
                                job_notification.prevhash,
                                job_notification.coinbase1,
                                job_notification.coinbase2,
                                job_notification.merkle_branches,
                                job_notification.version,
                                job_notification.nbits,
                                job_notification.ntime,
                                job_notification.clean_jobs
                            ]),
                        };

                        let job_notification_json =
                            match serde_json::to_string(&job_notification_response) {
                                Ok(json) => json,
                                Err(e) => {
                                    error!(error = %e, "Failed to serialize job notification");
                                    continue;
                                }
                            };
                        if let Err(e) = connection_info.sender.send(job_notification_json).await {
                            error!(
                                connection_id = %connection_id_hex,
                                peer = %peer_adr,
                                error = %e,
                                "Failed to send job to peer"
                            );
                        } else {
                            trace!(
                                connection_id = %connection_id_hex,
                                peer = %peer_adr,
                                job_id = %numeric_job_id,
                                "Dispatched job to peer"
                            );
                        }
                    }
                }

                NotifyCmd::SendLatestTemplateToNewDownstream {
                    new_downstream_addr,
                } => {
                    if let Some(cache_lock) = &upstream_cache {
                        let cache = cache_lock.read().await;
                        if let Some(job_notification) = cache.get_latest_job() {
                            info!(
                                "Sending cached upstream job {} to new miner {}",
                                job_notification.job_id, new_downstream_addr
                            );

                            let connection_entry = {
                                let current_downstream_mapping =
                                    downstream_connection_map.read().await;
                                current_downstream_mapping
                                    .downstream_channel_mapping
                                    .get(&new_downstream_addr)
                                    .cloned()
                            };

                            if let Some(connection_entry) = connection_entry {
                                match Self::send_upstream_job_notification_to_miner(
                                    &new_downstream_addr,
                                    &connection_entry,
                                    &job_notification,
                                    &self.job_store,
                                )
                                .await
                                {
                                    Ok(_) => {
                                        debug!(
                                            peer = %new_downstream_addr,
                                            "Successfully sent cached upstream job"
                                        );
                                    }
                                    Err(e) => {
                                        error!(
                                            peer = %new_downstream_addr,
                                            error = %e,
                                            "Failed to send cached upstream job"
                                        );
                                    }
                                }
                            } else {
                                warn!(
                                    peer = %new_downstream_addr,
                                    "Connection not found for new downstream"
                                );
                            }
                            continue;
                        }
                    }
                    let current_template_id = latest_template_id.lock().await.clone();
                    let connection_entry = {
                        let current_downstream_mapping = downstream_connection_map.read().await;
                        current_downstream_mapping
                            .downstream_channel_mapping
                            .get(&new_downstream_addr)
                            .cloned()
                    };
                    let connection_entry = match connection_entry {
                        Some(entry) => entry,
                        None => {
                            error!(peer = %new_downstream_addr, "Mining peer not found in connection mapping");
                            return Err(StratumErrors::PeerNotFoundInConnectionMapping {
                                peer_addr: new_downstream_addr,
                            });
                        }
                    };
                    let connection_id_hex = format!("{:x}", connection_entry.connection_id);

                    let is_empty_template = match current_template_id {
                        TemplateId::Braidpool(0) => true,
                        TemplateId::Upstream(ref s) if s == "0" => true,
                        _ => false,
                    };

                    if is_empty_template {
                        warn!(
                            connection_id = %connection_id_hex,
                            "No templates generated yet for new miner"
                        );
                        continue;
                    }

                    let (latest_template, latest_template_merkle_branch) = {
                        let template_guard = latest_template_arc.lock().await;
                        let merkle_guard = latest_template_merkle_branch_arc.lock().await;
                        (template_guard.clone(), merkle_guard.clone())
                    };
                    if latest_template.transactions.is_empty() {
                        warn!(
                            "Empty template for {}, will receive next upstream job",
                            new_downstream_addr
                        );
                        continue;
                    }
                    info!(
                        connection_id = %connection_id_hex,
                        template_id = %current_template_id,
                        "Sending existing latest template to new miner"
                    );

                    let clean_job = false;
                    let job_notification = Self::construct_job_notification(
                        clean_job,
                        latest_template.clone(),
                        current_template_id.clone(),
                        latest_template_merkle_branch,
                    )
                    .await;

                    let existing_job_id = self
                        .job_store
                        .lock()
                        .await
                        .latest_job_id_for(&current_template_id);

                    let serialized_notification: Result<String, StratumErrors> =
                        match job_notification {
                            Ok(job) => {
                                let numeric_job_id = match existing_job_id {
                                    Some(id) => id,
                                    None => {
                                        let unix_timestamp = {
                                            let current_system_time = std::time::SystemTime::now();
                                            match current_system_time.duration_since(UNIX_EPOCH) {
                                                Ok(duration) => match duration.as_secs().to_u32() {
                                                    Some(ts) => ts,
                                                    None => {
                                                        error!("System timestamp overflow for new miner notification");
                                                        continue;
                                                    }
                                                },
                                                Err(error) => {
                                                    return Err(StratumErrors::ErrorFetchingCurrentUNIXTimestamp {
                                                        error: error.to_string(),
                                                    })
                                                }
                                            }
                                        };
                                        let job_details = Self::build_local_job_details(
                                            &latest_template,
                                            &job,
                                            unix_timestamp,
                                        );
                                        self.job_store
                                            .lock()
                                            .await
                                            .insert(current_template_id, job_details)
                                    }
                                };
                                let job_notification_response = JobNotificationResponse {
                                    method: "mining.notify".to_string(),
                                    params: json!([
                                        numeric_job_id.to_string(),
                                        job.prevhash,
                                        job.coinbase1,
                                        job.coinbase2,
                                        job.merkle_branches,
                                        job.version,
                                        job.nbits,
                                        job.ntime,
                                        job.clean_jobs
                                    ]),
                                };
                                serde_json::to_string(&job_notification_response).map_err(|_| {
                                    StratumErrors::JobNotificationNotConstructed {
                                        job_template: latest_template.clone(),
                                    }
                                })
                            }
                            Err(error) => Err(error),
                        };
                    let job_notification = match serialized_notification {
                        Ok(job) => job,
                        Err(error) => {
                            error!(
                                error = %error,
                                "Error occurred while fetching the job notification"
                            );
                            return Err(error);
                        }
                    };
                    match connection_entry.sender.send(job_notification).await {
                        Ok(_) => {}
                        Err(error) => {
                            return Err(StratumErrors::NotifyMessageNotSent {
                                error: error.to_string(),
                                msg: error.0,
                                msg_type: "LatestTemplateSent".to_string(),
                            })
                        }
                    }
                }

                NotifyCmd::SendUpstreamJob { job_notification } => {
                    let compact_bits = match job_notification.parsed_bits {
                        Some(bits) => bits,
                        None => {
                            error!(
                                "Upstream job {} has no parsed bits, skipping...",
                                job_notification.job_id
                            );
                            error!("   Raw nbits from upstream: '{}'", job_notification.nbits);
                            continue;
                        }
                    };
                    let mut base_template = BlockTemplate::default();
                    base_template.bits = compact_bits;
                    if let Ok(version_u32) = u32::from_str_radix(&job_notification.version, 16) {
                        base_template.version =
                            bitcoin::block::Version::from_consensus(version_u32 as i32);
                    }
                    match hex::decode(&job_notification.prevhash) {
                        Ok(bytes) => {
                            if bytes.len() == 32 {
                                let mut hash_bytes = [0u8; 32];
                                hash_bytes.copy_from_slice(&bytes);
                                base_template.previousblockhash =
                                    bitcoin::BlockHash::from_byte_array(hash_bytes);
                            } else {
                                error!("Invalid upstream prevhash length: {}", bytes.len());
                                continue;
                            }
                        }
                        Err(e) => {
                            error!("Failed to decode upstream prevhash in notifier: {}", e);
                            continue;
                        }
                    }
                    let unix_timestamp = match u32::from_str_radix(&job_notification.ntime, 16) {
                        Ok(ts) => ts,
                        Err(e) => {
                            error!(
                                job_id = %job_notification.job_id,
                                ntime = %job_notification.ntime,
                                error = %e,
                                "Upstream job has malformed ntime, skipping broadcast"
                            );
                            continue;
                        }
                    };
                    let current_system_time = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_secs() as u32)
                        .unwrap_or(0);
                    base_template.curtime = unix_timestamp;

                    let downstream_channel_mapping = downstream_connection_map
                        .read()
                        .await
                        .downstream_channel_mapping
                        .clone();

                    let miner_count = downstream_channel_mapping.len();
                    if miner_count == 0 {
                        debug!(
                            job_id = %job_notification.job_id,
                            "No miners connected, skipping upstream job broadcast"
                        );
                        continue;
                    }

                    let template_id = TemplateId::from_upstream_string(&job_notification.job_id);
                    let job_details = Arc::new(JobDetails {
                        blocktemplate: base_template,
                        coinbase1: job_notification.coinbase1.clone(),
                        coinbase2: job_notification.coinbase2.clone(),
                        coinbase_merkle_path: job_notification.merkle_branches.clone(),
                        coinbase_witness_commitment: job_notification
                            .coinbase_witness_commitment
                            .clone(),
                        job_sent_time: current_system_time,
                        is_upstream_job: true,
                    });
                    self.job_store.lock().await.insert(template_id, job_details);

                    let upstream_job_id = &job_notification.job_id;

                    let job_notification_response = serde_json::json!({
                        "method": "mining.notify",
                        "params": [
                            upstream_job_id,
                            job_notification.prevhash,
                            job_notification.coinbase1,
                            job_notification.coinbase2,
                            job_notification.merkle_branches,
                            job_notification.version,
                            job_notification.nbits,
                            job_notification.ntime,
                            job_notification.clean_jobs
                        ]
                    });
                    let job_notification_str =
                        match serde_json::to_string(&job_notification_response) {
                            Ok(s) => s,
                            Err(e) => {
                                error!(error = %e, "Failed to serialize upstream job notification");
                                continue;
                            }
                        };
                    for (peer_addr, downstream_channel) in &downstream_channel_mapping {
                        if let Err(e) = downstream_channel
                            .sender
                            .send(job_notification_str.clone())
                            .await
                        {
                            error!("Failed to send upstream job to {}: {}", peer_addr, e);
                        } else {
                            info!(
                                "Sent upstream job {} to {} (bits: {})",
                                upstream_job_id, peer_addr, job_notification.nbits
                            );
                        }
                    }
                }

                NotifyCmd::UpdateExtranonce { new_bead_hash } => {
                    info!(
                        bead_hash = %new_bead_hash,
                        "Updating extranonce1 for all miners with new bead commitment"
                    );
                    use super::connection::ControlMsg;

                    let (
                        old_commitment_bytes,
                        new_commitment,
                        upstream_ext1_bytes,
                        downstream_mapping,
                        assigned_prefixes,
                    ) = {
                        let mut mapping = downstream_connection_map.write().await;
                        let old = mapping.current_bead_commitment.clone();
                        mapping.update_bead_commitment(new_bead_hash);
                        let new = mapping.get_current_bead_commitment();
                        let upstream = if let Some(ref s) = mapping.upstream_extranonce1 {
                            match hex::decode(s) {
                                Ok(bytes) => Some(bytes),
                                Err(e) => {
                                    error!(error = %e, upstream = %s, "Failed to decode upstream extranonce");
                                    None
                                }
                            }
                        } else {
                            None
                        };
                        let downstream = mapping.downstream_channel_mapping.clone();
                        let prefixes = mapping.assigned_prefixes.clone();
                        (old, new, upstream, downstream, prefixes)
                    };

                    if let Some(ref audit_dag_arc) = audit_dag {
                        let mut dag = audit_dag_arc.lock().await;
                        for (peer_addr, miner_state) in dag.miner_states.iter_mut() {
                            if miner_state.current_commitment.commitment_bytes
                                != new_commitment.as_slice()
                            {
                                miner_state.previous_commitment =
                                    Some(miner_state.current_commitment.clone());
                                miner_state.current_commitment =
                                    crate::audit::AuditCommitment::from_hash_prefix(
                                        &new_commitment,
                                    );
                                debug!(
                                    peer = %peer_addr,
                                    old = %hex::encode(&old_commitment_bytes),
                                    new = %hex::encode(&new_commitment),
                                    "Updated miner commitment with fallback"
                                );
                            } else {
                                debug!(peer = %peer_addr, "Skipping duplicate commitment update");
                            }
                        }
                    }

                    if let Some(upstream_bytes) = upstream_ext1_bytes {
                        let mut failed_peers = Vec::new();
                        for (peer_addr, connection_entry) in downstream_mapping.iter() {
                            if let Some(&prefix_u16) = assigned_prefixes.get(peer_addr) {
                                let prefix_bytes = prefix_u16.to_be_bytes().to_vec();
                                let mut new_extranonce1 = upstream_bytes.clone();
                                new_extranonce1.extend_from_slice(&prefix_bytes);
                                new_extranonce1.extend_from_slice(&new_commitment);

                                let new_extranonce1_hex = hex::encode(&new_extranonce1);
                                if let Err(e) = connection_entry.control_tx.try_send(
                                    ControlMsg::UpdateExtranonce(new_extranonce1.clone()),
                                ) {
                                    error!(peer = %peer_addr, "Failed to send internal control msg: {}. Flagging for disconnect.", e);
                                    failed_peers.push(peer_addr.clone());
                                    continue;
                                }
                                let set_extranonce_msg = serde_json::json!({
                                    "id": null,
                                    "method": "mining.set_extranonce",
                                    "params": [new_extranonce1_hex, 1]
                                });
                                if let Err(e) = connection_entry
                                    .sender
                                    .try_send(serde_json::to_string(&set_extranonce_msg).unwrap())
                                {
                                    error!(peer = %peer_addr, "Miner buffer full or closed. Disconnecting: {}", e);
                                    failed_peers.push(peer_addr.clone());
                                } else {
                                    info!(peer = %peer_addr, commitment = %hex::encode(&new_commitment), "Sent mining.set_extranonce");
                                }
                            }
                        }
                        if !failed_peers.is_empty() {
                            let mut mapping = downstream_connection_map.write().await;
                            for peer in failed_peers {
                                mapping.disconnect_peer(
                                    &peer,
                                    "Failed to update extranonce, stale connection",
                                );
                            }
                        }
                    } else {
                        warn!("Cannot update extranonce, upstream not configured");
                    }
                }

                NotifyCmd::BroadcastDifficulty { difficulty } => {
                    info!("Broadcasting difficulty {} to all miners", difficulty);

                    let set_difficulty_msg = serde_json::json!({
                        "method": "mining.set_difficulty",
                        "params": [difficulty]
                    });

                    let downstream_channel_mapping = downstream_connection_map
                        .read()
                        .await
                        .downstream_channel_mapping
                        .clone();

                    for (peer_addr, channel) in downstream_channel_mapping.iter() {
                        if let Err(e) = channel
                            .sender
                            .send(serde_json::to_string(&set_difficulty_msg).unwrap())
                            .await
                        {
                            error!("Failed to send difficulty to {}: {}", peer_addr, e);
                        } else {
                            info!("Sent difficulty {} to {}", difficulty, peer_addr);
                        }
                    }
                }
            }
        }

        warn!("Notifier channel closed, exiting...");
        Ok(())
    }
}
