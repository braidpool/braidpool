use std::{collections::VecDeque, sync::Arc};
use std::sync::atomic::{AtomicU32, Ordering};

use bitcoin::{absolute::Time, block::Header as BlockHeader, BlockHash, TxMerkleNode};
use bitcoin::consensus::Decodable;
use bitcoin::hashes::Hash;
use rand::RngCore;
use bitcoin::io::Cursor;
use bitcoin::Transaction;
use futures::lock::Mutex;
use serde_json::{json, Value};
use tokio::sync::{mpsc, RwLock};
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

use crate::config::PoolNetwork;
use crate::error::StratumErrors;
use crate::template_creator::calculate_merkle_root;
use crate::utils::compute_block_hash;
use crate::{SwarmHandler, EXTRANONCE2_SIZE};

use super::connection::ConnectionMapping;
use super::job_store::GlobalJobStore;
use super::notifier::NotifyCmd;
use super::types::{
    BlockSubmissionRequest, JobDetails, StandardResponse, SuggestDifficultyResponse,
    StratumResponses, StandardRequest,
};
use super::{
    COMMITMENT_SIZE, DEFAULT_VERSION_ROLLING_MASK,
    PREFIX_BYTES_SIZE, UPSTREAM_EXTRANONCE1_SIZE,
};

/// Downstream client state tracked per TCP connection.
///
/// Initialized during `mining.subscribe` / `mining.configure` / `mining.authorize`.
#[derive(Debug, Clone)]
pub struct DownstreamClient {
    pub authorized: bool,
    pub downstream_ip: String,
    pub subscribed: bool,
    pub suggest_difficulty_done: bool,
    pub channel_configured: bool,
    pub(super) connection_id: u32,
    pub(super) extranonce1: Vec<u8>,
    pub extranonce_history: VecDeque<Vec<u8>>,
    pub(super) version_rolling_mask: Option<String>,
    pub(super) version_rolling_min_bit: Option<u32>,
    pub(super) extranonce2_len: usize,
    /// Unique 2-byte prefix for audit-mode extranonce partitioning.
    /// Appended into extranonce1 sent to miner; prepended to extranonce2 sent upstream.
    pub extranonce2_prefix: Option<Vec<u8>>,
    pub miner_extranonce2_size: usize,
    pub monitor_target: Option<bitcoin::Target>,
    pub block_submission_tx: Option<mpsc::UnboundedSender<BlockSubmissionRequest>>,
    pub is_proxy_mode: bool,
    pub payout_address: Option<String>,
    pub audit_miner_difficulty: Option<f64>,
    pub network: PoolNetwork,
}

impl DownstreamClient {
    pub fn connection_id(&self) -> u32 {
        self.connection_id
    }

    /// Routes an incoming miner request to the appropriate handler.
    pub async fn handle_client_to_server_request(
        &mut self,
        client_request: StandardRequest,
        global_job_store: Arc<Mutex<GlobalJobStore>>,
        response_message_sender: mpsc::Sender<String>,
        notification_sender: mpsc::Sender<NotifyCmd>,
        peer_addr: String,
        swarm_handler: Arc<Mutex<SwarmHandler>>,
        audit_dag: Option<Arc<Mutex<crate::audit::AuditDAG>>>,
        upstream_share_tx: Option<mpsc::Sender<crate::upstream_pool::UpstreamShare>>,
        connection_mapping: Arc<RwLock<ConnectionMapping>>,
        upstream_configure_tx: Option<mpsc::Sender<(Value, u64, mpsc::Sender<Value>)>>,
    ) -> Result<StratumResponses, StratumErrors> {
        let req_params = client_request.params;
        let method = client_request.method.clone();
        let client_request_id = client_request.id;
        let connection_id_hex = format!("{:x}", self.connection_id());
        let response_or_error = match method.as_ref() {
            "mining.configure" => {
                self.handle_configure(&req_params, client_request_id, upstream_configure_tx)
                    .await
            }
            "mining.subscribe" => {
                Self::handle_subscribe(self, &req_params, client_request_id).await
            }
            "mining.authorize" => {
                self.handle_authorize(
                    &req_params,
                    client_request_id,
                    connection_mapping.clone(),
                    peer_addr.clone(),
                )
                .await
            }
            "mining.submit" => {
                let upstream_diff = {
                    let mapping = connection_mapping.read().await;
                    mapping.upstream_difficulty
                };
                Self::handle_submit(
                    self,
                    &req_params,
                    global_job_store,
                    client_request_id,
                    swarm_handler,
                    audit_dag,
                    upstream_share_tx,
                    upstream_diff,
                )
                .await
            }
            "mining.suggest_difficulty" => {
                if self.is_proxy_mode {
                    let upstream_diff = {
                        let mapping = connection_mapping.read().await;
                        mapping.upstream_difficulty
                    };
                    if let Some(diff) = upstream_diff {
                        info!(
                            connection_id = %connection_id_hex,
                            suggested = ?req_params,
                            upstream_diff = %diff,
                            "Audit mode, suggest_difficulty is taking place using upstream difficulty"
                        );
                        Ok(StratumResponses::SuggestDifficultyResponse {
                            suggest_difficulty_resp: SuggestDifficultyResponse {
                                method: "mining.set_difficulty".to_string(),
                                params: vec![diff as u64],
                            },
                        })
                    } else {
                        error!(
                            connection_id = %connection_id_hex,
                            "Audit mode: no upstream difficulty available, rejecting suggest_difficulty"
                        );
                        Err(StratumErrors::UpstreamNotReady {
                            error: "Upstream pool difficulty not available yet".to_string(),
                        })
                    }
                } else {
                    self.suggest_difficulty(&req_params).await
                }
            }
            method => Err(StratumErrors::InvalidMethod {
                method: method.to_string(),
            }),
        };
        match response_or_error {
            Ok(stratum_response) => {
                match &stratum_response {
                    StratumResponses::PendingUpstreamResponse => {
                        info!(
                            "Share forwarded to upstream, response pending (request_id={})",
                            client_request_id
                        );
                        return Ok(stratum_response);
                    }
                    _ => {}
                }
                let response_json_string = match stratum_response.clone() {
                    StratumResponses::StandardResponse { std_response } => {
                        serde_json::to_string(&std_response).map_err(|e| {
                            error!(error = %e, "Failed to serialize standard response");
                            StratumErrors::InvalidMethod {
                                method: "serialization_error".to_string(),
                            }
                        })?
                    }
                    StratumResponses::SuggestDifficultyResponse {
                        suggest_difficulty_resp,
                    } => serde_json::to_string(&suggest_difficulty_resp).unwrap(),
                    StratumResponses::PendingUpstreamResponse => {
                        return Ok(stratum_response);
                    }
                };
                debug!(
                    connection_id = %connection_id_hex,
                    method = %client_request.method,
                    response = %response_json_string,
                    "Sending response to downstream"
                );
                match response_message_sender.send(response_json_string).await {
                    Ok(_) => {
                        debug!(
                            connection_id = %connection_id_hex,
                            "Response sent to writer task"
                        );
                    }
                    Err(error) => {
                        error!(
                            connection_id = %connection_id_hex,
                            error = %error,
                            "Failed to send response to writer task"
                        );
                    }
                };

                if method == "mining.subscribe" {
                    let upstream_diff = {
                        let mapping = connection_mapping.read().await;
                        mapping.upstream_difficulty
                    };
                    if let Some(diff) = upstream_diff {
                        let miner_difficulty: f64 = if self.is_proxy_mode {
                            self.audit_miner_difficulty.unwrap_or(diff)
                        } else {
                            diff
                        };
                        let set_difficulty_msg = serde_json::json!({
                            "method": "mining.set_difficulty",
                            "params": [miner_difficulty]
                        });
                        if let Err(e) = response_message_sender
                            .send(serde_json::to_string(&set_difficulty_msg).unwrap())
                            .await
                        {
                            error!("Failed to send difficulty to miner: {}", e);
                        } else {
                            info!(
                                "Sent difficulty {} to miner {}",
                                miner_difficulty, peer_addr
                            );
                        }
                    }
                }
                if self.authorized == true
                    && self.subscribed == true
                    && method != "mining.submit"
                {
                    let notification_sent_res = notification_sender
                        .send(NotifyCmd::SendLatestTemplateToNewDownstream {
                            new_downstream_addr: peer_addr.clone(),
                        })
                        .await;
                    match notification_sent_res {
                        Ok(_) => {
                            debug!(
                                connection_id = %connection_id_hex,
                                peer_addr = %peer_addr,
                                "Requested latest template for new peer"
                            );
                        }
                        Err(error) => {
                            error!(
                                connection_id = %connection_id_hex,
                                error = %error,
                                peer_addr = %peer_addr,
                                "Failed to request latest template for new downstream"
                            );
                        }
                    }
                }
                Ok(stratum_response)
            }
            Err(error) => {
                error!(
                    connection_id = %connection_id_hex,
                    error = %error,
                    method = "handle_client_to_server_request",
                    "Failed to process client request"
                );
                Err(error)
            }
        }
    }

    /// Handles `mining.submit` from a downstream miner.
    ///
    /// Validates the share against the weak PoW target, reconstructs the coinbase,
    /// computes the Merkle root, and either submits the block or propagates the share.
    ///
    /// # Example Request
    /// ```
    /// use serde_json::json;
    /// let sample_request = json!({"id": 5, "method": "mining.submit",
    ///  "params": [
    ///      "bc1qnp980s5fpp8l94p5cvttmtdqy8rvrq74qly2yrfmzkdsntqzlc5qkc4rkq.bitaxe",
    ///      "2",
    ///      "09000000",
    ///      "6891e02b",
    ///      "91e70222",
    ///      "034ea000"
    ///  ]});
    /// ```
    pub async fn handle_submit(
        &mut self,
        submit_work_params: &Value,
        global_job_store: Arc<Mutex<GlobalJobStore>>,
        client_request_id: u64,
        swarm_handler: Arc<Mutex<SwarmHandler>>,
        audit_dag: Option<Arc<Mutex<crate::audit::AuditDAG>>>,
        upstream_share_tx: Option<mpsc::Sender<crate::upstream_pool::UpstreamShare>>,
        upstream_difficulty: Option<f64>,
    ) -> Result<StratumResponses, StratumErrors> {
        let connection_id_hex = format!("{:x}", self.connection_id());
        let param_array = match submit_work_params.as_array() {
            Some(param_array) => param_array,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                });
            }
        };
        if param_array.len() < 5 {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.submit".to_string(),
            });
        }
        let worker_name_res: Result<&str, StratumErrors> = match param_array.get(0) {
            Some(worker_name) => worker_name
                .as_str()
                .ok_or(StratumErrors::InvalidMethodParams {
                    method: "mining.submit: worker_name must be a string".to_string(),
                }),
            None => Err(StratumErrors::ParamNotFound {
                param: "worker_name".to_string(),
                method: "mining.submit".to_string(),
            }),
        };
        let worker_name = match worker_name_res {
            Ok(name) => name,
            Err(error) => return Err(error),
        };
        debug!(
            connection_id = %connection_id_hex,
            worker = %worker_name,
            "Mining worker connected"
        );
        if !self.authorized {
            warn!(
                "Miner {} tried to submit without authorization",
                worker_name
            );
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.submit".to_string(),
            });
        }

        let job_id_str = match param_array.get(1).and_then(|v| v.as_str()) {
            Some(id_str) => id_str,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "job_id".to_string(),
                    method: "mining.submit".to_string(),
                });
            }
        };

        let extranonce2: &str = match param_array.get(2).and_then(|v| v.as_str()) {
            Some(extra) => extra,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "extranonce2".to_string(),
                    method: "mining.submit".to_string(),
                })
            }
        };
        let expected_hex_len = self.miner_extranonce2_size * 2;
        if extranonce2.len() != expected_hex_len {
            error!(
                "Miner {} submitted extranonce2 '{}' with wrong length: expected {} hex chars, got {}",
                worker_name,
                extranonce2,
                expected_hex_len,
                extranonce2.len()
            );
            return Err(StratumErrors::InvalidMethodParams {
                method: format!(
                    "mining.submit: extranonce2 must be {} hex chars ({} bytes), got {}",
                    expected_hex_len,
                    self.miner_extranonce2_size,
                    extranonce2.len()
                ),
            });
        }

        debug!(
            worker = %worker_name,
            miner_extranonce2 = %extranonce2,
            extranonce1 = %hex::encode(&self.extranonce1),
            prefix_in_extranonce1 = ?self.extranonce2_prefix.as_ref().map(|p| hex::encode(p)),
            "Extranonce2 prefix handled via extranonce1; using miner-submitted extranonce2 unchanged"
        );

        if hex::decode(extranonce2).is_err() {
            error!(
                "Miner {} submitted invalid hex extranonce2: '{}'",
                worker_name, extranonce2
            );
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.submit: extranonce2 is not valid hex".to_string(),
            });
        }

        let ntime: &str = match param_array.get(3).and_then(|v| v.as_str()) {
            Some(nt) => nt,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "ntime".to_string(),
                    method: "mining.submit".to_string(),
                })
            }
        };

        let nonce: &str = match param_array.get(4).and_then(|v| v.as_str()) {
            Some(n) => n,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "nonce".to_string(),
                    method: "mining.submit".to_string(),
                })
            }
        };

        let rolled_version_bits: Option<&str> = param_array.get(5).and_then(|v| v.as_str());

        let (submitted_job, template_id) = {
            let job_mapping = global_job_store.lock().await;

            if let Ok((job, tid)) = job_mapping.get_by_string_job_id(job_id_str) {
                debug!(
                    jobid = job_id_str,
                    mode = "upstream",
                    "Found job by string ID"
                );
                (job, tid)
            } else {
                let numeric_job_id = match job_id_str.parse::<u64>() {
                    Ok(id) => id,
                    Err(_) => {
                        match u64::from_str_radix(job_id_str, 16) {
                            Ok(id) => id,
                            Err(e) => {
                                return Err(StratumErrors::JobIdCouldNotBeParsed {
                                    method: "mining.submit".to_string(),
                                    error: format!("Invalid job_id (not valid decimal, hex, or upstream): {}, {}", job_id_str, e),
                                });
                            }
                        }
                    }
                };
                info!(
                    jobid = numeric_job_id,
                    mode = "braidpool",
                    "Found job by numeric ID"
                );
                let job = job_mapping.get_by_job_id(numeric_job_id)?;
                let templateid = job_mapping
                    .template_id_from_job_id(numeric_job_id)
                    .ok_or_else(|| StratumErrors::MiningJobNotFound {
                        job_id: Some(numeric_job_id),
                        template_id: None,
                    })?;
                (job, templateid)
            }
        };

        if submitted_job.is_upstream_job {
            return self
                .validate_and_forward_upstream_share(
                    &connection_id_hex,
                    worker_name,
                    job_id_str,
                    extranonce2,
                    ntime,
                    nonce,
                    rolled_version_bits,
                    &submitted_job,
                    client_request_id,
                    audit_dag,
                    upstream_share_tx,
                    upstream_difficulty,
                )
                .await;
        }

        let ntime_u32 = match u32::from_str_radix(ntime, 16) {
            Ok(v) => v,
            Err(e) => {
                error!(connection_id = %connection_id_hex, error = %e, ntime = %ntime, "Failed to parse ntime");
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                });
            }
        };
        let nonce_u32 = match u32::from_str_radix(nonce, 16) {
            Ok(v) => v,
            Err(e) => {
                error!(connection_id = %connection_id_hex, error = %e, nonce = %nonce, "Failed to parse nonce");
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                });
            }
        };

        let extranonce_1_hex = hex::encode(self.extranonce1.clone());
        let coinbase_tx_hex = format!(
            "{}{}{}{}",
            submitted_job.coinbase1,
            extranonce_1_hex,
            extranonce2.to_ascii_lowercase(),
            submitted_job.coinbase2
        );
        let coinbase_bytes = match hex::decode(&coinbase_tx_hex) {
            Ok(bytes) => bytes,
            Err(e) => {
                error!(connection_id = %connection_id_hex, error = %e, "Failed to decode coinbase hex");
                return Err(StratumErrors::InvalidCoinbase);
            }
        };

        debug!(
            connection_id = %connection_id_hex,
            coinbase_hex = %hex::encode(&coinbase_bytes),
            "Reconstructed coinbase transaction"
        );

        let mut coinbase_cursor = Cursor::new(coinbase_bytes);
        let mut coinbase_tx: Transaction =
            match bitcoin::Transaction::consensus_decode(&mut coinbase_cursor) {
                Ok(tx) => tx,
                Err(e) => {
                    error!(connection_id = %connection_id_hex, error = %e, "Failed to decode coinbase transaction");
                    return Err(StratumErrors::InvalidCoinbase);
                }
            };

        let mut merkle_branches_bytes: Vec<Vec<u8>> = Vec::new();
        for merkle_branch in submitted_job.coinbase_merkle_path.clone() {
            let mut merkle_branch_bytes: [u8; 32] = [0u8; 32];
            if let Err(e) = hex::decode_to_slice(&merkle_branch, &mut merkle_branch_bytes) {
                error!(connection_id = %connection_id_hex, error = %e, merkle_branch = %merkle_branch, "Failed to decode merkle branch hex");
                return Err(StratumErrors::InvalidCoinbase);
            }
            merkle_branches_bytes.push(Vec::from(merkle_branch_bytes));
        }
        let merkle_root_bytes =
            calculate_merkle_root(coinbase_tx.compute_txid(), merkle_branches_bytes.as_slice());
        let merkle_root = TxMerkleNode::from_byte_array(merkle_root_bytes);

        let header_version =
            bitcoin::block::Version::to_consensus(submitted_job.blocktemplate.version.clone());
        let mut final_masked_version =
            bitcoin::block::Version::to_consensus(submitted_job.blocktemplate.version);

        if let Some(mask_hex) = self.version_rolling_mask.as_ref() {
            let rolled_version_bits: &str = match param_array.get(5).and_then(|v| v.as_str()) {
                Some(n) => n,
                None => {
                    return Err(StratumErrors::ParamNotFound {
                        param: "rolled_version_bits".to_string(),
                        method: "mining.submit".to_string(),
                    })
                }
            };

            let mut rolled_version = [0u8; 4];
            match hex::decode_to_slice(rolled_version_bits, &mut rolled_version) {
                Ok(_) => (),
                Err(e) => {
                    return Err(StratumErrors::VersionRollingHexParseError {
                        error: e.to_string(),
                    })
                }
            }
            let version_bits = i32::from_be_bytes(rolled_version);

            let mut mask_bytes = [0u8; 4];
            hex::decode_to_slice(mask_hex, &mut mask_bytes).map_err(|e| {
                StratumErrors::VersionRollingHexParseError {
                    error: e.to_string(),
                }
            })?;
            let mask_version_bits = i32::from_be_bytes(mask_bytes);

            let precondition = version_bits & !mask_version_bits;
            if precondition != 0 {
                return Err(StratumErrors::MaskNotValid {
                    error: "version_bits & !mask_version_bits must be equal to Zero".to_string(),
                });
            }
            final_masked_version =
                (header_version & !mask_version_bits) | (version_bits & mask_version_bits);
        }
        let header = BlockHeader {
            version: bitcoin::blockdata::block::Version::from_consensus(final_masked_version),
            prev_blockhash: submitted_job.blocktemplate.previousblockhash,
            merkle_root: merkle_root,
            time: ntime_u32,
            bits: submitted_job.blocktemplate.bits,
            nonce: nonce_u32,
        };
        let compact_target = submitted_job.blocktemplate.bits;
        let target = bitcoin::Target::from_compact(compact_target);
        debug!(
            connection_id = %connection_id_hex,
            target = %hex::encode(target.to_be_bytes()),
            "Mining target"
        );
        debug!(
            connection_id = %connection_id_hex,
            block_hash = %compute_block_hash(&header, self.network),
            "Block hash computed"
        );

        let coinbase_txid_be_hex = hex::encode(coinbase_tx.compute_txid().to_byte_array());
        let version_be_hex = {
            let v = header.version.to_consensus() as u32;
            hex::encode(v.to_be_bytes())
        };
        let prevhash_be_hex = hex::encode(header.prev_blockhash.to_byte_array());
        let merkle_root_be_hex = hex::encode(header.merkle_root.to_byte_array());
        let time_be_hex = hex::encode(header.time.to_be_bytes());
        let bits_be_hex = hex::encode(header.bits.to_consensus().to_be_bytes());
        let nonce_be_hex = hex::encode(header.nonce.to_be_bytes());

        debug!(
            connection_id = %connection_id_hex,
            coinbase_txid = %coinbase_txid_be_hex,
            version = %version_be_hex,
            prev_blockhash = %prevhash_be_hex,
            merkle_root = %merkle_root_be_hex,
            time = %time_be_hex,
            bits = %bits_be_hex,
            nonce = %nonce_be_hex,
            "Block header fields for submission"
        );
        let witness = match &submitted_job.coinbase_witness_commitment {
            Some(w) => w.to_vec(),
            None => {
                error!(
                    connection_id = %connection_id_hex,
                    job_id = job_id_str,
                    "Job missing witness commitment"
                );
                return Err(StratumErrors::InvalidCoinbase);
            }
        };
        let witness_bytes = match witness.get(0) {
            Some(w) => w,
            None => {
                error!(connection_id = %connection_id_hex, "Witness commitment is empty");
                return Err(StratumErrors::InvalidCoinbase);
            }
        };
        match coinbase_tx.input.get_mut(0) {
            Some(input) => input.witness.push(witness_bytes),
            None => {
                error!(connection_id = %connection_id_hex, "Coinbase transaction has no inputs");
                return Err(StratumErrors::InvalidCoinbase);
            }
        };
        let coinbase_tx_for_submission = coinbase_tx.clone();
        let mut block_transactions = vec![coinbase_tx];
        block_transactions.extend(submitted_job.blocktemplate.transactions.clone());

        let complete_block = bitcoin::Block {
            header,
            txdata: block_transactions,
        };

        let pow_result = if self.network.is_cpunet() {
            let block_hash = self.network.block_hash(&header);
            if target.is_met_by(block_hash) {
                Ok(block_hash)
            } else {
                Err(bitcoin::block::ValidationError::BadProofOfWork)
            }
        } else {
            header.validate_pow(target)
        };

        match pow_result {
            Ok(block_hash) => {
                debug!(
                    connection_id = %connection_id_hex,
                    target = %target,
                    hash = %block_hash,
                    is_cpunet = self.network.is_cpunet(),
                    "Header meets target"
                );

                if let Some(ref submission_tx) = self.block_submission_tx {
                    let submission = BlockSubmissionRequest {
                        template_id: template_id.clone(),
                        header: header.clone(),
                        coinbase_transaction: coinbase_tx_for_submission.clone(),
                    };

                    match submission_tx.send(submission) {
                        Ok(_) => {
                            debug!(
                                connection_id = %connection_id_hex,
                                template_id = %template_id,
                                "Block sent to submission handler"
                            );
                        }
                        Err(e) => {
                            error!(
                                connection_id = %connection_id_hex,
                                error = %e,
                                template_id = %template_id,
                                "Failed to send block submission"
                            );
                        }
                    }
                } else {
                    warn!(
                        connection_id = %connection_id_hex,
                        context = "block_submission",
                        template_id = %template_id,
                        "Channel unavailable - cannot forward valid block"
                    );
                }
            }
            Err(e) => {
                warn!(
                    connection_id = %connection_id_hex,
                    error = %e,
                    target = %target,
                    "Header does not meet target"
                );
                return Ok(StratumResponses::StandardResponse {
                    std_response: StandardResponse::new_ok(Some(client_request_id), json!(false)),
                });
            }
        }
        let extranonce_2_raw_value = match u64::from_str_radix(extranonce2, 16) {
            Ok(v) => v,
            Err(e) => {
                error!(connection_id = %connection_id_hex, error = %e, extranonce2 = %extranonce2, "Failed to parse extranonce2");
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                });
            }
        };
        let extranonce_1_hex_str = hex::encode(self.extranonce1.clone());
        let extranonce_1_raw_value = match u64::from_str_radix(&extranonce_1_hex_str, 16) {
            Ok(v) => v,
            Err(e) => {
                error!(connection_id = %connection_id_hex, error = %e, extranonce1 = %extranonce_1_hex_str, "Failed to parse extranonce1");
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                });
            }
        };
        let _swarm_command_sent = match swarm_handler
            .lock()
            .await
            .propagate_valid_bead(
                complete_block,
                extranonce_2_raw_value,
                &self.downstream_ip,
                submitted_job.job_sent_time,
                worker_name,
                extranonce_1_raw_value,
            )
            .await
        {
            Ok(_) => {
                info!(
                    connection_id = %connection_id_hex,
                    job_id = job_id_str,
                    template_id = %template_id,
                    peer = %self.downstream_ip,
                    "Candidate block submitted"
                );
                Ok(StratumResponses::StandardResponse {
                    std_response: StandardResponse::new_ok(Some(client_request_id), json!(true)),
                })
            }
            Err(error) => Err(error),
        };
        Ok(StratumResponses::StandardResponse {
            std_response: StandardResponse::new_ok(Some(client_request_id), json!(true)),
        })
    }

    /// Validates an upstream job share, constructs a bead, and forwards to the upstream pool if valid.
    async fn validate_and_forward_upstream_share(
        &self,
        connection_id_hex: &str,
        worker_name: &str,
        job_id_str: &str,
        extranonce2: &str,
        ntime: &str,
        nonce: &str,
        rolled_version_bits: Option<&str>,
        submitted_job: &JobDetails,
        client_request_id: u64,
        audit_dag: Option<Arc<Mutex<crate::audit::AuditDAG>>>,
        upstream_share_tx: Option<mpsc::Sender<crate::upstream_pool::UpstreamShare>>,
        upstream_difficulty: Option<f64>,
    ) -> Result<StratumResponses, StratumErrors> {
        let ntime_u32 =
            u32::from_str_radix(ntime, 16).map_err(|e| StratumErrors::InvalidMethodParams {
                method: format!("mining.submit: invalid ntime hex: {}", e),
            })?;

        let nonce_u32 =
            u32::from_str_radix(nonce, 16).map_err(|e| StratumErrors::InvalidMethodParams {
                method: format!("mining.submit: invalid nonce hex: {}", e),
            })?;

        let raw_bytes = submitted_job
            .blocktemplate
            .previousblockhash
            .to_byte_array();
        let mut prevhash_for_header = [0u8; 32];

        for chunk_idx in 0..8 {
            let offset = chunk_idx * 4;
            prevhash_for_header[offset] = raw_bytes[offset + 3];
            prevhash_for_header[offset + 1] = raw_bytes[offset + 2];
            prevhash_for_header[offset + 2] = raw_bytes[offset + 1];
            prevhash_for_header[offset + 3] = raw_bytes[offset];
        }

        let base_version = submitted_job.blocktemplate.version.to_consensus();
        let final_version = if let Some(rolled_hex) = rolled_version_bits {
            let rolled = u32::from_str_radix(rolled_hex, 16).unwrap_or(0) as i32;
            let mask = self
                .version_rolling_mask
                .as_ref()
                .and_then(|s| u32::from_str_radix(s, 16).ok())
                .unwrap_or(DEFAULT_VERSION_ROLLING_MASK) as i32;
            (base_version & !mask) | (rolled & mask)
        } else {
            base_version
        };

        let mut valid_header = None;
        let mut valid_block_hash = None;
        let mut used_extranonce1 = vec![];
        let mut meets_upstream = false;
        let mut candidates = vec![self.extranonce1.clone()];
        candidates.extend(self.extranonce_history.iter().cloned());
        let miner_difficulty = if self.is_proxy_mode {
            self.audit_miner_difficulty.or(upstream_difficulty)
        } else {
            None
        }
        .unwrap_or(100.0);
        let miner_target = Self::target_from_difficulty(miner_difficulty);
        let upstream_target = upstream_difficulty
            .map(|d| Self::target_from_difficulty(d))
            .unwrap_or_else(|| bitcoin::Target::from_compact(submitted_job.blocktemplate.bits));

        for (idx, extranonce1_candidate) in candidates.iter().enumerate() {
            let coinbase_tx_hex = format!(
                "{}{}{}{}",
                submitted_job.coinbase1,
                hex::encode(extranonce1_candidate),
                extranonce2.to_ascii_lowercase(),
                submitted_job.coinbase2
            );
            let coinbase_bytes = match hex::decode(&coinbase_tx_hex) {
                Ok(b) => b,
                Err(_) => continue,
            };
            let mut cursor = Cursor::new(coinbase_bytes);
            let coinbase_tx: Transaction =
                match bitcoin::Transaction::consensus_decode(&mut cursor) {
                    Ok(tx) => tx,
                    Err(_) => continue,
                };

            let mut merkle_branches_bytes: Vec<Vec<u8>> = Vec::new();
            for merkle_branch in &submitted_job.coinbase_merkle_path {
                let mut bytes = [0u8; 32];
                if hex::decode_to_slice(merkle_branch, &mut bytes).is_err() {
                    continue;
                }
                merkle_branches_bytes.push(bytes.to_vec());
            }
            let merkle_root_bytes =
                calculate_merkle_root(coinbase_tx.compute_txid(), &merkle_branches_bytes);
            let merkle_root = TxMerkleNode::from_byte_array(merkle_root_bytes);
            let header = BlockHeader {
                version: bitcoin::block::Version::from_consensus(final_version),
                prev_blockhash: BlockHash::from_byte_array(prevhash_for_header),
                merkle_root,
                time: ntime_u32,
                bits: submitted_job.blocktemplate.bits,
                nonce: nonce_u32,
            };
            let header_bytes = bitcoin::consensus::serialize(&header);
            let block_hash_d = bitcoin::hashes::sha256d::Hash::hash(&header_bytes);
            let block_hash = bitcoin::BlockHash::from_byte_array(block_hash_d.to_byte_array());

            if Self::validate_share_against_target(block_hash, &miner_target) {
                valid_header = Some(header);
                valid_block_hash = Some(block_hash);
                used_extranonce1 = extranonce1_candidate.clone();
                meets_upstream = Self::validate_share_against_target(block_hash, &upstream_target);
                let miner_target = miner_target.to_be_bytes();
                let miner_target_hex = hex::encode(miner_target);
                let upstream_target_hex = hex::encode(upstream_target.to_be_bytes());
                debug!(
                    connection_id = %connection_id_hex,
                    worker = %worker_name,
                    job_id = %job_id_str,
                    block_hash = %block_hash,
                    miner_target = %miner_target_hex,
                    upstream_target = %upstream_target_hex,
                    meets_miner_diff = true,
                    meets_upstream_diff = %meets_upstream,
                    "Share difficulty validation results"
                );
                if idx > 0 {
                    debug!(
                        "Valid upstream share found using extranonce1 (Depth: {})",
                        idx
                    );
                }
                break;
            }
        }

        if let (Some(header), Some(block_hash)) = (valid_header, valid_block_hash) {
            let share_id = block_hash;
            let upstream_ext1_size = used_extranonce1
                .len()
                .checked_sub(PREFIX_BYTES_SIZE + COMMITMENT_SIZE)
                .ok_or_else(|| StratumErrors::InvalidMethodParams {
                    method: "mining.submit: extranonce1 too short for audit mode".to_string(),
                })?;

            if upstream_ext1_size != 4 && upstream_ext1_size != 8 {
                return Err(StratumErrors::InvalidMethodParams {
                    method: format!(
                        "mining.submit: unsupported upstream ext1 size: {}",
                        upstream_ext1_size
                    ),
                });
            }

            let bead = {
                let payout_address = self
                    .payout_address
                    .as_ref()
                    .ok_or_else(|| StratumErrors::InvalidMethodParams {
                        method: "mining.submit: payout address not set".to_string(),
                    })?
                    .parse::<bitcoin::Address<bitcoin::address::NetworkUnchecked>>()
                    .map_err(|e| {
                        error!(
                            worker = %worker_name,
                            error = %e,
                            "Invalid payout address during share submission"
                        );
                        StratumErrors::InvalidMethodParams {
                            method: format!("mining.submit: invalid payout address: {}", e),
                        }
                    })?
                    .require_network(bitcoin::Network::Bitcoin)
                    .map_err(|e| {
                        error!(
                            worker = %worker_name,
                            error = ?e,
                            "Payout address network mismatch, please use mainnet address"
                        );
                        StratumErrors::InvalidMethodParams {
                            method: format!("mining.submit: address is for wrong network: {:?}", e),
                        }
                    })?
                    .to_string();

                let (parent_hash_set, time_hash_set) = {
                    let mut parents: Vec<crate::utils::BeadHash> = Vec::new();
                    let mut timestamps = crate::committed_metadata::TimeVec(Vec::new());

                    if let Some(ref dag_mutex) = audit_dag {
                        let dag = dag_mutex.lock().await;
                        let mut pairs: Vec<(crate::utils::BeadHash, bitcoin::absolute::Time)> = dag
                            .active_parents
                            .iter()
                            .map(|&(_, block_hash, parent_time)| {
                                (crate::utils::BeadHash::from(block_hash), parent_time)
                            })
                            .collect();
                        pairs.sort_by_key(|(hash, _)| *hash);
                        for (hash, time) in pairs {
                            parents.push(hash);
                            timestamps.0.push(time);
                        }
                    }
                    if parents.is_empty() {
                        info!(worker = %worker_name, "Genesis bead, no parents exist");
                    }
                    (parents, timestamps)
                };

                let weak_target = miner_target.to_compact_lossy();
                let min_target = upstream_difficulty
                    .map(|d| Self::target_from_difficulty(d).to_compact_lossy())
                    .unwrap_or(submitted_job.blocktemplate.bits);
                debug!(
                    worker = %worker_name,
                    weak_target_bits = %format!("{:08x}", weak_target.to_consensus()),
                    min_target_bits = %format!("{:08x}", min_target.to_consensus()),
                    upstream_difficulty = ?upstream_difficulty,
                    "Calculated bead difficulty targets"
                );
                let public_key =
                    "020202020202020202020202020202020202020202020202020202020202020202"
                        .parse::<bitcoin::PublicKey>()
                        .unwrap();
                let job_time =
                    bitcoin::absolute::Time::from_consensus(submitted_job.job_sent_time)
                        .map_err(|e| {
                            error!(
                                worker = %worker_name,
                                error = %e,
                                "Invalid job timestamp"
                            );
                            StratumErrors::InvalidMethodParams {
                                method: format!("mining.submit: invalid job timestamp: {}", e),
                            }
                        })?;

                let committed_metadata = crate::committed_metadata::CommittedMetadata {
                    comm_pub_key: public_key,
                    miner_ip: self.downstream_ip.clone(),
                    start_timestamp: job_time,
                    transaction_ids: crate::committed_metadata::TxIdVec(Vec::new()),
                    parents: parent_hash_set,
                    parent_bead_timestamps: time_hash_set,
                    payout_address: payout_address,
                    min_target,
                    weak_target,
                };

                let broadcast_time = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map_err(|e| e.to_string())
                    .and_then(|d| {
                        let ts: u32 = d
                            .as_secs()
                            .try_into()
                            .map_err(|e: std::num::TryFromIntError| e.to_string())?;
                        Time::from_consensus(ts).map_err(|e| e.to_string())
                    })
                    .map_err(|e| StratumErrors::ErrorFetchingCurrentUNIXTimestamp { error: e })?;

                let (extranonce_1_raw_value, extranonce_2_raw_value) = {
                    let upstream_bytes = &used_extranonce1[..upstream_ext1_size];

                    let extra_nonce_1: u64 = if upstream_ext1_size == 8 {
                        u64::from_be_bytes(upstream_bytes.try_into().unwrap())
                    } else {
                        u32::from_be_bytes(upstream_bytes.try_into().unwrap()) as u64
                    };

                    let audit_portion = &used_extranonce1[upstream_ext1_size..];
                    let miner_roll_bytes =
                        hex::decode(extranonce2).map_err(|e| StratumErrors::InvalidMethodParams {
                            method: format!("mining.submit: invalid extranonce2 hex: {}", e),
                        })?;
                    let mut nonce2_buf = [0u8; 8];
                    let audit_len = audit_portion.len().min(PREFIX_BYTES_SIZE + COMMITMENT_SIZE);
                    nonce2_buf[..audit_len].copy_from_slice(&audit_portion[..audit_len]);
                    let roll_len = miner_roll_bytes
                        .len()
                        .min(std::mem::size_of::<u64>() - audit_len);
                    nonce2_buf[audit_len..audit_len + roll_len]
                        .copy_from_slice(&miner_roll_bytes[..roll_len]);
                    let extra_nonce_2 = u64::from_be_bytes(nonce2_buf);

                    debug!(
                        worker = %worker_name,
                        upstream_ext1_size = %upstream_ext1_size,
                        upstream_ext1 = %hex::encode(upstream_bytes),
                        extra_nonce_1 = %format!("{:016x}", extra_nonce_1),
                        audit_portion = %hex::encode(audit_portion),
                        miner_roll = %extranonce2,
                        extra_nonce_2 = %format!("{:016x}", extra_nonce_2),
                        "Packed extranonce values for bead metadata"
                    );

                    (extra_nonce_1, extra_nonce_2)
                };

                let placeholder_sig_bytes = [0u8; 64];
                let sig = bitcoin::ecdsa::Signature {
                    signature: bitcoin::secp256k1::ecdsa::Signature::from_compact(
                        &placeholder_sig_bytes,
                    )
                    .expect("Valid placeholder signature"),
                    sighash_type: bitcoin::EcdsaSighashType::All,
                };

                let uncommitted_metadata = crate::uncommitted_metadata::UnCommittedMetadata {
                    broadcast_timestamp: broadcast_time,
                    extra_nonce_1: extranonce_1_raw_value,
                    extra_nonce_2: extranonce_2_raw_value,
                    signature: sig,
                };

                let bead = crate::bead::Bead {
                    committed_metadata,
                    block_header: header,
                    uncommitted_metadata,
                };

                debug!(
                    worker = %worker_name,
                    block_hash = %bead.block_header.block_hash(),
                    parent_count = %bead.committed_metadata.parents.len(),
                    parents = ?bead.committed_metadata.parents.iter().map(|p| format!("{:?}", p)).collect::<Vec<_>>(),
                    weak_target = %format!("{:08x}", bead.committed_metadata.weak_target.to_consensus()),
                    min_target = %format!("{:08x}", bead.committed_metadata.min_target.to_consensus()),
                    "Constructed audit mode bead"
                );
                bead
            };

            let audit_record = crate::audit::AuditRecord {
                share_id: share_id.clone(),
                timestamp: std::time::SystemTime::now(),
                miner_ip: self.downstream_ip.clone(),
                worker_name: worker_name.to_string(),
                job_id: job_id_str.to_string(),
                extranonce2: extranonce2.to_string(),
                nonce: nonce.to_string(),
                ntime: ntime.to_string(),
                audit_verified: false,
                audit_commitment: None,
                upstream_accepted: None,
                upstream_eligible: meets_upstream,
                bead_hash: block_hash,
            };

            if let Some(ref audit_dag_arc) = audit_dag {
                let mut dag = audit_dag_arc.lock().await;
                match dag
                    .add_and_record_bead(audit_record, bead, &used_extranonce1)
                    .await
                {
                    Ok((_, bead_added)) => {
                        if !bead_added {
                            warn!("Bead already in DAG, rejecting share and skipping upstream forward");
                            return Ok(StratumResponses::StandardResponse {
                                std_response: StandardResponse::new_ok(
                                    Some(client_request_id),
                                    json!(false),
                                ),
                            });
                        }
                        if meets_upstream {
                            if let Some(ref upstream_tx) = upstream_share_tx {
                                dag.mark_upstream_forwarded(&share_id);
                                drop(dag);
                                let full_extranonce2 = if let Some(ref prefix) =
                                    self.extranonce2_prefix
                                {
                                    let commitment_start = upstream_ext1_size + PREFIX_BYTES_SIZE;
                                    let commitment_end = commitment_start + COMMITMENT_SIZE;
                                    if used_extranonce1.len() < commitment_end {
                                        error!(
                                            worker = %worker_name,
                                            extranonce1_len = %used_extranonce1.len(),
                                            required = %commitment_end,
                                            "Extranonce1 too short"
                                        );
                                        return Err(StratumErrors::InvalidMethodParams {
                                            method: "mining.submit: malformed extranonce1"
                                                .to_string(),
                                        });
                                    }
                                    let commitment = hex::encode(
                                        &used_extranonce1[commitment_start..commitment_end],
                                    );
                                    format!("{}{}{}", hex::encode(prefix), commitment, extranonce2)
                                } else {
                                    extranonce2.to_string()
                                };
                                let upstream_share = crate::upstream_pool::UpstreamShare {
                                    worker_name: worker_name.to_string(),
                                    job_id: job_id_str.to_string(),
                                    extranonce2: full_extranonce2,
                                    ntime: ntime.to_string(),
                                    nonce: nonce.to_string(),
                                    version_bits: rolled_version_bits.map(String::from),
                                    original_request_id: client_request_id,
                                    share_id: share_id.clone(),
                                };
                                if let Err(e) = upstream_tx.send(upstream_share).await {
                                    error!("Failed to forward to upstream: {}", e);
                                    return Ok(StratumResponses::StandardResponse {
                                        std_response: StandardResponse::new_ok(
                                            Some(client_request_id),
                                            json!(false),
                                        ),
                                    });
                                } else {
                                    return Ok(StratumResponses::StandardResponse {
                                        std_response: StandardResponse::new_ok(
                                            Some(client_request_id),
                                            json!(true),
                                        ),
                                    });
                                }
                            }
                        }
                    }
                    Err(e) => {
                        warn!("Audit DAG rejected bead: {}", e);
                        return Ok(StratumResponses::StandardResponse {
                            std_response: StandardResponse::new_ok(
                                Some(client_request_id),
                                json!(false),
                            ),
                        });
                    }
                }
            }
            return Ok(StratumResponses::StandardResponse {
                std_response: StandardResponse::new_ok(Some(client_request_id), json!(true)),
            });
        } else {
            warn!("Share below minimum difficulty");
            return Ok(StratumResponses::StandardResponse {
                std_response: StandardResponse::new_ok(Some(client_request_id), json!(false)),
            });
        }
    }

    pub(super) fn target_from_difficulty(difficulty: f64) -> bitcoin::Target {
        if difficulty < 1.0 || !difficulty.is_finite() {
            return bitcoin::Target::from_compact(bitcoin::CompactTarget::from_consensus(
                0x1d00ffff,
            ));
        }

        let diff1_target =
            bitcoin::Target::from_compact(bitcoin::CompactTarget::from_consensus(0x1d00ffff));

        let mut diff1_f64: f64 = 0.0;
        let diff1_bytes = diff1_target.to_le_bytes();
        for (i, byte) in diff1_bytes.iter().enumerate() {
            diff1_f64 += (*byte as f64) * 256.0f64.powi(i as i32);
        }

        let new_target_val = diff1_f64 / difficulty;
        let mut le_bytes = [0u8; 32];
        let mut v = new_target_val;
        for i in (0..32).rev() {
            let power = 256.0f64.powi(i as i32);
            let byte_val = (v / power).floor();
            if byte_val >= 256.0 {
                le_bytes[i] = 0xff;
            } else {
                le_bytes[i] = byte_val as u8;
            }
            v -= le_bytes[i] as f64 * power;
        }
        bitcoin::Target::from_le_bytes(le_bytes)
    }

    fn validate_share_against_target(block_hash: BlockHash, target: &bitcoin::Target) -> bool {
        target.is_met_by(block_hash)
    }

    /// Handles `mining.set_difficulty` from a downstream miner.
    pub async fn suggest_difficulty(
        &mut self,
        suggest_difficulty_params: &Value,
    ) -> Result<StratumResponses, StratumErrors> {
        if let Some(difficulty) = suggest_difficulty_params.get(0) {
            info!(
                connection_id = %format!("{:x}", self.connection_id()),
                params = ?suggest_difficulty_params,
                "Handling suggested difficulty"
            );
            let difficulty_u64 = difficulty
                .as_u64()
                .ok_or(StratumErrors::InvalidMethodParams {
                    method: "mining.set_difficulty".to_string(),
                })?;
            self.suggest_difficulty_done = true;
            Ok(StratumResponses::SuggestDifficultyResponse {
                suggest_difficulty_resp: SuggestDifficultyResponse {
                    method: "mining.set_difficulty".to_string(),
                    params: vec![difficulty_u64],
                },
            })
        } else {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.set_difficulty".to_string(),
            });
        }
    }

    /// Handles `mining.authorize` from a downstream miner.
    pub async fn handle_authorize(
        &mut self,
        authorize_request_params: &Value,
        client_request_id: u64,
        connection_mapping: Arc<RwLock<ConnectionMapping>>,
        peer_addr: String,
    ) -> Result<StratumResponses, StratumErrors> {
        let connection_id_hex = format!("{:x}", self.connection_id());
        debug!(
            connection_id = %connection_id_hex,
            params = ?authorize_request_params,
            "Authorization request"
        );
        let param_array = match authorize_request_params.as_array() {
            Some(param_array) => param_array,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.authorize".to_string(),
                });
            }
        };
        let username_res: Result<&str, StratumErrors> = match param_array.get(0) {
            Some(user) => match user.as_str() {
                Some(username_str) => Ok(username_str),
                None => Err(StratumErrors::ParamNotFound {
                    param: "username must be a string".to_string(),
                    method: "mining.authorize".to_string(),
                }),
            },
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "username".to_string(),
                    method: "mining.authorize".to_string(),
                });
            }
        };
        let username = match username_res {
            Ok(username_value) => username_value,
            Err(error) => {
                return Err(error);
            }
        };

        let bitcoin_address = if let Some(dot_pos) = username.rfind('.') {
            username[..dot_pos].to_string()
        } else {
            username.to_string()
        };

        self.payout_address = Some(bitcoin_address.clone());
        self.authorized = true;
        info!(
            connection_id = %connection_id_hex,
            username = %username,
            payout_address = %bitcoin_address,
            "Miner authorized"
        );
        let mut conn_map = connection_mapping.write().await;
        conn_map.register_worker(peer_addr.clone(), username.to_string());
        drop(conn_map);
        info!("Registered worker '{}' for peer {}", username, peer_addr);

        Ok(StratumResponses::StandardResponse {
            std_response: (StandardResponse {
                id: Some(client_request_id),
                result: Some(json!(true)),
                error: None,
            }),
        })
    }

    /// Handles `mining.configure` (BIP 310 feature negotiation).
    pub async fn handle_configure(
        &mut self,
        config_req_params: &Value,
        client_request_id: u64,
        upstream_configure_tx: Option<mpsc::Sender<(Value, u64, mpsc::Sender<Value>)>>,
    ) -> Result<StratumResponses, StratumErrors> {
        let connection_id_hex = format!("{:x}", self.connection_id());
        info!(
            connection_id = %connection_id_hex,
            params = ?config_req_params,
            "Configuration handling is taking place"
        );

        match &upstream_configure_tx {
            Some(_) => debug!("Audit mode: upstream_configure_tx available"),
            None => warn!("No upstream_configure_tx, using local handling"),
        }
        if let Some(ref upstream_tx) = upstream_configure_tx {
            debug!("Forwarding mining.configure to upstream pool");
            let (response_tx, mut response_rx) = mpsc::channel(1);

            if let Err(e) = upstream_tx
                .send((config_req_params.clone(), client_request_id, response_tx))
                .await
            {
                error!("Failed to forward configure to upstream: {}", e);
                return Err(StratumErrors::UpstreamShareForwardFailed {
                    error: e.to_string(),
                });
            }

            match tokio::time::timeout(std::time::Duration::from_secs(10), response_rx.recv()).await
            {
                Ok(Some(response)) => {
                    info!("Received upstream configure response: {:?}", response);

                    if let Some(result) = response.get("result").and_then(|r| r.as_object()) {
                        if let Some(mask) =
                            result.get("version-rolling.mask").and_then(|m| m.as_str())
                        {
                            self.version_rolling_mask = Some(mask.to_string());
                            info!("Using upstream version_rolling_mask: {}", mask);
                        }
                        if let Some(min_bits) = result.get("version-rolling.min-bit-count") {
                            if let Some(count) = min_bits.as_u64() {
                                self.version_rolling_min_bit = Some(count as u32);
                            }
                        }
                    }

                    self.channel_configured = true;

                    return Ok(StratumResponses::StandardResponse {
                        std_response: StandardResponse {
                            id: Some(client_request_id),
                            result: response.get("result").cloned(),
                            error: response
                                .get("error")
                                .and_then(|e| e.as_str())
                                .map(String::from),
                        },
                    });
                }
                Ok(None) => {
                    error!("Upstream configure channel closed");
                    return Err(StratumErrors::UpstreamShareForwardFailed {
                        error: "Upstream channel closed".to_string(),
                    });
                }
                Err(_) => {
                    error!("Upstream configure request timed out");
                    return Err(StratumErrors::UpstreamShareForwardFailed {
                        error: "Timeout waiting for upstream response".to_string(),
                    });
                }
            }
        }

        let params = match config_req_params.as_array() {
            Some(param_array) => param_array,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.configure".to_string(),
                });
            }
        };
        if params.len() != 2 {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.configure".to_string(),
            });
        }

        let features = match params[0].as_array() {
            Some(feature_arr) => feature_arr,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "feature_array".to_string(),
                    method: "mining.configure".to_string(),
                })
            }
        };
        let feature_names: Vec<String> = match features
            .iter()
            .map(|f| f.as_str().map(|s| s.to_string()))
            .collect::<Option<Vec<String>>>()
        {
            Some(feature_arr) => feature_arr,
            None => {
                return Err(StratumErrors::ConfigureFeatureStringConversion {
                    error: "Json value could not be converted to string in while handling mining.configure ".to_string(),
                })
            }
        };
        info!(
            connection_id = %connection_id_hex,
            features = ?feature_names,
            "Mining features requested"
        );
        let config_map = match params[1].as_object() {
            Some(con_map) => con_map,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "configuration_map".to_string(),
                    method: "mining.config".to_string(),
                });
            }
        };
        info!(
            connection_id = %connection_id_hex,
            config = ?config_map,
            "Configuration map processed"
        );
        #[allow(unused)]
        let minimum_difficulty = config_map.get("minimum-difficulty.value").or(None);
        let version_rolling_mask = config_map.get("version-rolling.mask").or(None);
        let version_rolling_min_bit_count =
            config_map.get("version-rolling.min-bit-count").or(None);
        if let Some(mask_value) = version_rolling_mask {
            let mut mask_bytes: [u8; 4] = [0u8; 4];
            let version_rolling_mask_str = match mask_value.as_str() {
                Some(version_str) => version_str,
                None => {
                    return Err(StratumErrors::VersionRollingStringParseError {
                        error: "Version rolling mask could not be converted to string from provided bytes".to_string(),
                    });
                }
            };
            match hex::decode_to_slice(version_rolling_mask_str, &mut mask_bytes) {
                Ok(_) => {}
                Err(error) => {
                    return Err(StratumErrors::VersionRollingHexParseError {
                        error: error.to_string(),
                    });
                }
            };
            let final_rollable_version_bits = u32::from_be_bytes(mask_bytes) & 0x1FFFE000;
            self.version_rolling_mask = Some(format!("{:08x}", final_rollable_version_bits));
            info!(
                "Set version_rolling_mask: {:08x}",
                final_rollable_version_bits
            );
        }
        if let Some(min_bit_count_value) = version_rolling_min_bit_count {
            let mut mask_bytes: [u8; 4] = [0u8; 4];
            let version_rolling_min_bit_count_str = match min_bit_count_value.as_str() {
                Some(s) => s,
                None => {
                    return Err(StratumErrors::VersionrollingMinBitCountHexParseError {
                        error: "version-rolling.min-bit-count is not a string".to_string(),
                    });
                }
            };
            match hex::decode_to_slice(version_rolling_min_bit_count_str, &mut mask_bytes) {
                Ok(_) => {}
                Err(error) => {
                    return Err(StratumErrors::VersionrollingMinBitCountHexParseError {
                        error: error.to_string(),
                    });
                }
            };
            self.version_rolling_min_bit = Some(u32::from_be_bytes(mask_bytes));
        }
        self.channel_configured = true;
        Ok(StratumResponses::StandardResponse {
            std_response: StandardResponse {
                id: Some(client_request_id),
                result: Some(json!({
                    "minimum-difficulty":false,
                    "version-rolling": true,
                    "version-rolling.mask":self.version_rolling_mask.clone().unwrap_or("1fffe000".to_string()),
                    "version-rolling.min-bit-count":self.version_rolling_min_bit.unwrap_or(0)
                })),
                error: None,
            },
        })
    }

    /// Handles `mining.subscribe` and returns session identifiers.
    pub async fn handle_subscribe(
        &mut self,
        subscribe_req_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        info!(
            connection_id = %format!("{:x}", self.connection_id()),
            params = ?subscribe_req_params,
            "Miner subscribing"
        );
        let subscriptions: Vec<(String, String)> = vec![
            (String::from("mining.set_difficulty"), String::from("34")),
            (String::from("mining.notify"), String::from("12")),
        ];
        self.subscribed = true;
        let extranonce1_hex_str = hex::encode(&self.extranonce1);

        let extranonce2_size_for_miner = if self.extranonce2_prefix.is_some() {
            self.miner_extranonce2_size
        } else {
            self.extranonce2_len
        };
        info!(
            "Subscribe response: mode={}, extranonce1={}, extranonce2_size={}, prefix={:?}",
            if self.is_proxy_mode {
                "AUDIT"
            } else {
                "BRAIDPOOL"
            },
            extranonce1_hex_str,
            extranonce2_size_for_miner,
            self.extranonce2_prefix.as_ref().map(|p| hex::encode(p))
        );

        Ok(StratumResponses::StandardResponse {
            std_response: StandardResponse::new_ok(
                Some(client_request_id),
                json!([
                    subscriptions,
                    extranonce1_hex_str,
                    extranonce2_size_for_miner
                ]),
            ),
        })
    }
}

static NEXT_CONNECTION_ID: AtomicU32 = AtomicU32::new(0);

impl DownstreamClient {
    pub fn new(network: PoolNetwork) -> Self {
        let connection_id = NEXT_CONNECTION_ID.fetch_add(1, Ordering::SeqCst);
        let mut extranonce1_bytes = [0; UPSTREAM_EXTRANONCE1_SIZE];
        rand::thread_rng().fill_bytes(&mut extranonce1_bytes);
        let extranonce1_hex = hex::encode(&extranonce1_bytes);
        debug!(
            connection_id = %format!("{:x}", connection_id),
            extranonce1 = %extranonce1_hex,
            "Generated extranonce1 for new downstream connection"
        );
        DownstreamClient {
            authorized: false,
            downstream_ip: "0.0.0.0".to_string(),
            subscribed: false,
            suggest_difficulty_done: false,
            channel_configured: false,
            connection_id,
            extranonce1: Vec::from(extranonce1_bytes),
            extranonce_history: VecDeque::new(),
            version_rolling_mask: None,
            version_rolling_min_bit: None,
            extranonce2_len: EXTRANONCE2_SIZE,
            extranonce2_prefix: None,
            miner_extranonce2_size: EXTRANONCE2_SIZE,
            monitor_target: None,
            block_submission_tx: None,
            network,
            is_proxy_mode: false,
            payout_address: None,
            audit_miner_difficulty: None,
        }
    }
}
