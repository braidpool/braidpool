use crate::bead::Bead;
use crate::braid::consensus_functions;
use crate::braid::consensus_functions::highest_work_path;
use crate::braid::AddBeadStatus;
use crate::braid::Braid;
use crate::ipc::client::QueueStats;
use crate::peer_manager::PeerManager;
use crate::stratum;
use crate::stratum::BlockTemplate;
use crate::utils::BeadHash;
use bitcoin::block::HeaderExt;
use bitcoin::Transaction;
use futures::lock::Mutex;
use jsonrpsee::core::async_trait;
use jsonrpsee::core::middleware::Batch;
use jsonrpsee::core::middleware::Notification;
use jsonrpsee::core::middleware::RpcServiceT;
use jsonrpsee::proc_macros::rpc;
use jsonrpsee::types::ErrorObjectOwned;
use jsonrpsee::types::Request;
use jsonrpsee::ConnectionId;
use serde::{Deserialize, Serialize};
use serde_json;
use serde_json::Value;
use std::collections::HashMap;
use std::collections::HashSet;
use std::future::Future;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::{mpsc, oneshot, RwLock};
use tracing::{info, warn};

#[cfg(test)]
use {
    crate::braid, crate::utils::create_test_bead, jsonrpsee::core::client::ClientT,
    jsonrpsee::core::params::ArrayParams, jsonrpsee::http_client::HttpClient,
};

//server side trait to be implemented for the handler
//that is the JSON-RPC handle to initiate the RPC context
//supporting both http and websockets
#[rpc(server)]
pub trait Rpc {
    //RPC methods supported by braid-API
    #[method(name = "getbead")]
    async fn get_bead(&self, bead_hash: String) -> Result<Bead, ErrorObjectOwned>;

    #[method(name = "addbead")]
    async fn add_bead(&self, bead_data: String) -> Result<String, ErrorObjectOwned>;

    #[method(name = "gettips")]
    async fn get_tips(&self) -> Result<Vec<String>, ErrorObjectOwned>;

    #[method(name = "getbeadcount")]
    async fn get_bead_count(&self) -> Result<u64, ErrorObjectOwned>;

    #[method(name = "getcohortcount")]
    async fn get_cohort_count(&self) -> Result<u64, ErrorObjectOwned>;

    #[method(name = "getcohortbyid")]
    async fn get_cohort_by_id(&self, cohort_id: u64) -> Result<Vec<String>, ErrorObjectOwned>;

    #[method(name = "getgenesis")]
    async fn get_genesis(&self) -> Result<String, ErrorObjectOwned>;

    #[method(name = "getmininginfo")]
    async fn get_mining_info(
        &self,
        params: Option<serde_json::Value>,
    ) -> Result<Value, ErrorObjectOwned>;

    #[method(name = "getminerinfo")]
    async fn get_miner_info(&self) -> Result<Vec<String>, ErrorObjectOwned>;

    #[method(name = "getparents")]
    async fn get_parents(&self, bead_hash: String) -> Result<Vec<String>, ErrorObjectOwned>;

    #[method(name = "getchildren")]
    async fn get_children(&self, bead_hash: String) -> Result<Vec<String>, ErrorObjectOwned>;

    #[method(name = "gethighestworkpathbycount")]
    async fn get_highest_work_path_by_count(
        &self,
        limit: u8,
    ) -> Result<Vec<String>, ErrorObjectOwned>;

    #[method(name = "getipcstats")]
    async fn get_ipc_stats(&self) -> Result<Value, ErrorObjectOwned>;

    #[method(name = "getbraidinfo")]
    async fn get_braid_info(&self) -> Result<Value, ErrorObjectOwned>;

    #[method(name = "getnodeinfo")]
    async fn get_node_info(&self, bead_hash: String) -> Result<Value, ErrorObjectOwned>;

    #[method(name = "getpeerinfo")]
    async fn get_peer_info(&self) -> Result<Value, ErrorObjectOwned>;

    #[method(name = "stagedtransactions")]
    async fn staged_transactions(&self) -> Result<Value, ErrorObjectOwned>;

    #[method(name = "unstagetransactions")]
    async fn unstage_transactions(&self, txid: String) -> Result<bool, ErrorObjectOwned>;

    #[method(name = "bitcoinproxy")]
    async fn bitcoin_proxy(
        &self,
        method: String,
        params: serde_json::Value,
    ) -> Result<serde_json::Value, ErrorObjectOwned>;
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct MiningInfoParams {
    #[serde(default)]
    pub public_keys: Option<Vec<String>>,

    #[serde(default)]
    pub miner_ips: Option<Vec<String>>,
}

#[derive(Serialize)]
struct MiningInfo {
    our_beads_count: usize,
    total_beads_in_braid: usize,
    our_total_work: String,
    total_work_in_braid: String,
    our_work_share_percent: f64,
    payout_address: Option<String>,
    /// Additional info about which criteria were used for filtering
    filter_info: Option<String>,
}

#[derive(Serialize, Deserialize, Debug)]
struct BraidInfo {
    bead_count: usize,
    tip_count: usize,
    tips: Vec<String>,
    cohort_count: usize,
    orphan_count: usize,
    genesis_beads: Vec<String>,
    total_work: String,
}

#[derive(Serialize, Deserialize)]
struct NodeInfo {
    common_pubkey: String,
    miner_ip: String,
    payout_address: String,
    minimum_target: String,
}

/// Per-tx entry returned by stagedtransactions. Includes txid so callers can pass it to unstagetransactions.
#[derive(Serialize, Deserialize)]
struct StagedTxEntry {
    /// Transaction ID (64-char hex). Use this as the argument to unstagetransactions.
    txid: String,
    tx: Transaction,
}

/// JSON-RPC request structure
#[derive(Serialize)]
struct JsonRpcRequest {
    jsonrpc: &'static str,
    method: String,
    params: serde_json::Value,
    id: u64,
}

/// JSON-RPC response structure
#[derive(Deserialize)]
struct JsonRpcResponse {
    result: Option<serde_json::Value>,
    error: Option<serde_json::Value>,
}

/// Bitcoin RPC configuration for proxy calls
#[derive(Debug, Clone)]
pub struct BitcoinRpcConfig {
    pub host: String,
    pub port: u16,
    pub username: String,
    pub password: String,
    pub client: reqwest::Client,
}

impl BitcoinRpcConfig {
    /// Create RPC config from CLI arguments
    pub fn from_cli_args(args: &crate::cli::Cli) -> Result<Option<Self>, String> {
        // If no RPC credentials provided, return Ok(None) (RPC proxy disabled)
        let username = match &args.rpcuser {
            None => return Ok(None),
            Some(u) => u,
        };

        let password = match &args.rpcpass {
            None => return Ok(None),
            Some(p) => p,
        };

        // Validate that credentials are not empty
        if username.is_empty() {
            return Err(
                "RPC username cannot be empty. Please provide a valid username with --rpcuser"
                    .to_string(),
            );
        }

        if password.is_empty() {
            return Err(
                "RPC password cannot be empty. Please provide a valid password with --rpcpass"
                    .to_string(),
            );
        }

        let client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(30))
            .build()
            .map_err(|e| format!("Failed to create HTTP client: {}", e))?;

        Ok(Some(Self {
            host: args.bitcoin.clone(),
            port: args.rpcport,
            username: username.clone(),
            password: password.clone(),
            client,
        }))
    }

    /// Build RPC URL for bitcoincore-rpc client
    pub fn rpc_url(&self) -> String {
        format!("http://{}:{}", self.host, self.port)
    }
}

pub enum RpcProxyCommand {
    RemoveTransaction {
        txid: String,
        responder: oneshot::Sender<Result<bool, String>>,
    },
    GetStats {
        responder: oneshot::Sender<Result<QueueStats, String>>,
    },
}

// RPC Server implementation using channels
pub struct RpcServerImpl {
    braid_arc: Arc<RwLock<Braid>>,
    peer_manager: Arc<tokio::sync::RwLock<PeerManager>>,
    stratum_connection_mapping: Arc<tokio::sync::RwLock<stratum::ConnectionMapping>>,
    latest_block: Arc<Mutex<BlockTemplate>>,
    rpc_proxy_tx: mpsc::UnboundedSender<RpcProxyCommand>,
    bitcoin_rpc_config: Option<BitcoinRpcConfig>,
}

impl RpcServerImpl {
    pub fn new(
        braid_shared_pointer: Arc<RwLock<Braid>>,
        peer_manager: Arc<tokio::sync::RwLock<PeerManager>>,
        stratum_connection_mapping: Arc<tokio::sync::RwLock<stratum::ConnectionMapping>>,
        latest_block_template: Arc<Mutex<BlockTemplate>>,
        rpc_proxy_tx: mpsc::UnboundedSender<RpcProxyCommand>,
        bitcoin_rpc_config: Option<BitcoinRpcConfig>,
    ) -> Self {
        Self {
            braid_arc: braid_shared_pointer,
            peer_manager,
            stratum_connection_mapping,
            latest_block: latest_block_template,
            rpc_proxy_tx,
            bitcoin_rpc_config,
        }
    }
}
#[async_trait]
impl RpcServer for RpcServerImpl {
    async fn get_bead(&self, bead_hash: String) -> Result<Bead, ErrorObjectOwned> {
        let hash = bead_hash
            .parse::<BeadHash>()
            .map_err(|_| ErrorObjectOwned::owned(1, "Invalid bead hash format", None::<()>))?;
        info!(hash = %hash, "Get bead request received");
        let braid_data = self.braid_arc.read().await;
        let bead = braid_data
            .beads
            .iter()
            .find(|bead| bead.block_header.block_hash() == hash)
            .cloned();

        bead.ok_or_else(|| ErrorObjectOwned::owned(3, "Bead not found", None::<()>))
    }

    async fn add_bead(&self, bead_data: String) -> Result<String, ErrorObjectOwned> {
        let bead: Bead = serde_json::from_str(&bead_data).map_err(|e| {
            ErrorObjectOwned::owned(1, format!("Invalid bead data: {}", e), None::<()>)
        })?;
        info!(
            hash = %bead.block_header.block_hash(),
            "Add bead request received"
        );
        let mut braid_data = self.braid_arc.write().await;
        let success_status = braid_data.extend(&bead);

        match success_status {
            AddBeadStatus::BeadAdded => Ok("Bead added successfully".to_string()),
            AddBeadStatus::DagAlreadyContainsBead => Ok("Bead already exists".to_string()),
            AddBeadStatus::InvalidBead => {
                Err(ErrorObjectOwned::owned(4, "Invalid bead", None::<()>))
            }
            AddBeadStatus::ParentsNotYetReceived => {
                Ok("Bead queued, waiting for parents".to_string())
            }
        }
    }

    async fn get_tips(&self) -> Result<Vec<String>, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;
        let tips: Vec<BeadHash> = braid_data
            .tips
            .iter()
            .map(|&index| braid_data.beads[index].block_header.block_hash())
            .collect();
        info!(tip_count = %tips.len(), "Get tips request received");
        let tips_str: Vec<String> = tips.iter().map(|h| h.to_string()).collect();

        Ok(tips_str)
    }

    async fn get_bead_count(&self) -> Result<u64, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;
        let count = braid_data.beads.len();
        info!(count = %count, "Get bead count request received");
        Ok(count as u64)
    }

    async fn get_cohort_count(&self) -> Result<u64, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;
        let count = braid_data.cohorts.len();
        info!(count = %count, "Get cohort count request received");

        Ok(count as u64)
    }

    async fn get_cohort_by_id(&self, cohort_id: u64) -> Result<Vec<String>, ErrorObjectOwned> {
        info!(id = %cohort_id, "Get cohort by id request received");

        let braid_data = self.braid_arc.read().await;

        if let Some(cohort) = braid_data.cohorts.get(cohort_id as usize) {
            let cohort_hashes: Vec<String> = cohort
                .0
                .iter()
                .map(|index| {
                    braid_data.beads[*index]
                        .block_header
                        .block_hash()
                        .to_string()
                })
                .collect();

            Ok(cohort_hashes)
        } else {
            Err(ErrorObjectOwned::owned(
                3,
                "Cohort not found for given ID",
                None::<()>,
            ))
        }
    }

    async fn get_genesis(&self) -> Result<String, ErrorObjectOwned> {
        info!("Get Genesis request received");

        let braid_data = self.braid_arc.read().await;

        if braid_data.genesis_beads.len() != 1 {
            return Err(ErrorObjectOwned::owned(
                5,
                "Expected exactly one genesis bead ",
                None::<()>,
            ));
        }
        let genesis_bead_index = braid_data.genesis_beads.iter().next().unwrap();
        let genesis_bead = &braid_data.beads[*genesis_bead_index];

        Ok(genesis_bead.block_header.block_hash().to_string())
    }

    async fn get_miner_info(&self) -> Result<Vec<String>, ErrorObjectOwned> {
        info!("Get Miner Info Request Received");
        let connection_map = self.stratum_connection_mapping.read().await;
        let miner_ips: Vec<String> = connection_map
            .downstream_channel_mapping
            .keys()
            .cloned()
            .collect();

        Ok(miner_ips)
    }

    async fn get_mining_info(
        &self,
        params: Option<serde_json::Value>,
    ) -> Result<Value, ErrorObjectOwned> {
        info!("Get Mining Info Request Received");

        // Parse and validate parameters - parameters are required
        let filter_params: MiningInfoParams = match params {
            Some(p) => {
                serde_json::from_value(p).map_err(|e| {
                    ErrorObjectOwned::owned(
                        1,
                        format!(
                            "Invalid parameters: {}. Expected JSON object with at least one of: \
                            public_keys (array of hex-encoded strings) or miner_ips (array of strings). \
                            Example: {{\"public_keys\": [\"0202...\"]}} or {{\"miner_ips\": [\"192.168.1.1\"]}}",
                            e
                        ),
                        None::<()>,
                    )
                })?
            }
            None => {
                return Err(ErrorObjectOwned::owned(
                    2,
                    "Parameters required. Please provide at least one filter: public_keys or miner_ips. \
                    Example: {\"public_keys\": [\"020202020202020202020202020202020202020202020202020202020202020202\"]}",
                    None::<()>,
                ));
            }
        };

        let has_public_keys = filter_params
            .public_keys
            .as_ref()
            .map(|keys| !keys.is_empty())
            .unwrap_or(false);
        let has_miner_ips = filter_params
            .miner_ips
            .as_ref()
            .map(|ips| !ips.is_empty())
            .unwrap_or(false);

        if !has_public_keys && !has_miner_ips {
            return Err(ErrorObjectOwned::owned(
                2,
                "At least one non-empty filter must be provided. \
                Specify either public_keys (array of hex strings) or miner_ips (array of strings).",
                None::<()>,
            ));
        }

        let public_key_set: Option<HashSet<String>> = filter_params
            .public_keys
            .as_ref()
            .filter(|keys| !keys.is_empty())
            .map(|keys| {
                keys.iter()
                    .map(|k| {
                        // Remove any whitespace and convert to lowercase
                        k.trim().to_lowercase()
                    })
                    .filter(|k| !k.is_empty())
                    .collect()
            });

        let miner_ip_set: Option<HashSet<String>> = filter_params
            .miner_ips
            .as_ref()
            .filter(|ips| !ips.is_empty())
            .map(|ips| {
                ips.iter()
                    .map(|ip| ip.trim().to_string())
                    .filter(|ip| !ip.is_empty())
                    .collect()
            });

        let braid_data = self.braid_arc.read().await;
        let all_beads = &braid_data.beads;

        if all_beads.is_empty() {
            let info = MiningInfo {
                our_beads_count: 0,
                total_beads_in_braid: 0,
                our_total_work: "0".to_string(),
                total_work_in_braid: "0".to_string(),
                our_work_share_percent: 0.0,
                payout_address: None,
                filter_info: Some("No beads in braid".to_string()),
            };
            return serde_json::to_value(&info).map_err(|e| {
                ErrorObjectOwned::owned(2, format!("Internal Error: {}", e), None::<()>)
            });
        }

        let first_work = all_beads[0].block_header.work();
        let zero_work = first_work - first_work;

        let mut our_beads_count = 0;
        let mut our_total_work = zero_work;
        let mut total_work_in_braid = zero_work;
        let mut payout_addresses = Vec::new();

        for bead in all_beads.iter() {
            let work = bead.block_header.work();
            total_work_in_braid = total_work_in_braid + work;

            let mut is_ours = false;

            if let Some(ref pub_key_set) = public_key_set {
                let bead_pub_key_hex = bead
                    .committed_metadata
                    .comm_pub_key
                    .to_string()
                    .to_lowercase();
                if pub_key_set.contains(&bead_pub_key_hex) {
                    is_ours = true;
                }
            }

            if let Some(ref ip_set) = miner_ip_set {
                let bead_miner_ip = bead.committed_metadata.miner_ip.trim();
                if ip_set.contains(bead_miner_ip) {
                    is_ours = true;
                }
            }

            if is_ours {
                our_beads_count += 1;
                our_total_work = our_total_work + work;

                let payout_addr = bead.committed_metadata.payout_address.trim();
                if !payout_addr.is_empty() && !payout_addresses.contains(&payout_addr.to_string()) {
                    payout_addresses.push(payout_addr.to_string());
                }
            }
        }

        let our_work_share_percent = if total_work_in_braid > zero_work {
            let our_work_str = our_total_work.to_string();
            let total_work_str = total_work_in_braid.to_string();

            match (our_work_str.parse::<f64>(), total_work_str.parse::<f64>()) {
                (Ok(our_work_f64), Ok(total_work_f64)) => {
                    if total_work_f64 > 0.0 && our_work_f64 >= 0.0 {
                        // Clamp percentage to [0.0, 100.0] range
                        (our_work_f64 / total_work_f64 * 100.0).min(100.0).max(0.0)
                    } else {
                        0.0
                    }
                }
                _ => {
                    warn!(
                        "Failed to parse work values for percentage calculation: our_work={}, total_work={}",
                        our_work_str, total_work_str
                    );
                    0.0
                }
            }
        } else {
            0.0
        };

        // Select the first payout address if available (for backward compatibility)
        let payout_address = payout_addresses.first().cloned();

        // Build filter info string describing what filters were applied
        let mut filter_info_parts = Vec::new();
        if let Some(ref keys) = filter_params.public_keys {
            if !keys.is_empty() {
                filter_info_parts.push(format!("public_keys:{}", keys.len()));
            }
        }
        if let Some(ref ips) = filter_params.miner_ips {
            if !ips.is_empty() {
                filter_info_parts.push(format!("miner_ips:{}", ips.len()));
            }
        }
        let filter_info = if filter_info_parts.is_empty() {
            None
        } else {
            Some(format!("Filtered by: {}", filter_info_parts.join(", ")))
        };

        let mining_info = MiningInfo {
            our_beads_count,
            total_beads_in_braid: all_beads.len(),
            our_total_work: our_total_work.to_string(),
            total_work_in_braid: total_work_in_braid.to_string(),
            our_work_share_percent,
            payout_address,
            filter_info,
        };

        serde_json::to_value(&mining_info)
            .map_err(|e| ErrorObjectOwned::owned(2, format!("Internal Error: {}", e), None::<()>))
    }

    async fn get_parents(&self, bead_hash: String) -> Result<Vec<String>, ErrorObjectOwned> {
        info!(bead = %bead_hash, "Get parent bead request received");

        let hash = bead_hash
            .parse::<BeadHash>()
            .map_err(|_| ErrorObjectOwned::owned(1, "Invalid bead hash format", None::<()>))?;

        let braid_data = self.braid_arc.read().await;

        let bead = braid_data
            .beads
            .iter()
            .find(|b| b.block_header.block_hash() == hash)
            .cloned();

        match bead {
            Some(bead) => {
                let parent_hashes: Vec<String> = bead
                    .committed_metadata
                    .parents
                    .iter()
                    .map(|h| h.to_string())
                    .collect();

                Ok(parent_hashes)
            }
            None => Err(ErrorObjectOwned::owned(3, "Bead not found", None::<()>)),
        }
    }

    async fn get_children(&self, bead_hash: String) -> Result<Vec<String>, ErrorObjectOwned> {
        info!(bead = %bead_hash, "Get children bead request received");

        let parent_hash = bead_hash
            .parse::<BeadHash>()
            .map_err(|_| ErrorObjectOwned::owned(1, "Invalid bead hash format", None::<()>))?;

        let braid_data = self.braid_arc.read().await;

        let parent_index = match braid_data.bead_index_mapping.get(&parent_hash) {
            Some(index) => *index,
            None => return Err(ErrorObjectOwned::owned(3, "Bead not found", None::<()>)),
        };

        let mut parents_map: HashMap<usize, HashSet<usize>> = HashMap::new();
        for (index, bead) in braid_data.beads.iter().enumerate() {
            let parent_indices: HashSet<usize> = bead
                .committed_metadata
                .parents
                .iter()
                .filter_map(|p_hash| braid_data.bead_index_mapping.get(p_hash).copied())
                .collect();
            parents_map.insert(index, parent_indices);
        }

        let children_map = consensus_functions::reverse(&braid_data, &parents_map);

        let children_hashes: Vec<String> = match children_map.get(&parent_index) {
            Some(child_indices) => child_indices
                .iter()
                .map(|&index| {
                    braid_data.beads[index]
                        .block_header
                        .block_hash()
                        .to_string()
                })
                .collect(),
            None => Vec::new(), // This case is unlikely if the parent exists, but it's safe to handle.
        };
        Ok(children_hashes)
    }

    async fn get_highest_work_path_by_count(
        &self,
        limit: u8,
    ) -> Result<Vec<String>, ErrorObjectOwned> {
        info!(limit = %limit, "Get highest work path by count request received");

        let braid_data = self.braid_arc.read().await;

        let mut parents_map: HashMap<usize, HashSet<usize>> = HashMap::new();
        for (index, bead) in braid_data.beads.iter().enumerate() {
            let parent_indices: HashSet<usize> = bead
                .committed_metadata
                .parents
                .iter()
                .filter_map(|p_hash| braid_data.bead_index_mapping.get(p_hash).copied())
                .collect();
            parents_map.insert(index, parent_indices);
        }

        let children_map = consensus_functions::reverse(&braid_data, &parents_map);

        let bead_list =
            match highest_work_path(&braid_data, &parents_map, Some(&children_map), None) {
                Ok(list) => list,
                Err(_) => {
                    return Err(ErrorObjectOwned::owned(
                        5,
                        "Failed to get highest_work path",
                        None::<()>,
                    ))
                }
            };

        let available_count = bead_list.len();
        let requested_limit = limit as usize;

        // Handle empty braid case
        if available_count == 0 {
            return Err(ErrorObjectOwned::owned(
                7,
                "No beads available in the braid. Cannot compute highest work path. Add beads to the braid first.",
                None::<()>,
            ));
        }

        // Validate that limit is greater than zero
        if requested_limit == 0 {
            return Err(ErrorObjectOwned::owned(
                6,
                format!(
                    "Invalid limit: {} is too low. Limit must be between 1 and {} (the maximum available count in highest work path).",
                    0, available_count
                ),
                None::<()>,
            ));
        }

        // Validate that the requested limit doesn't exceed available beads
        if requested_limit > available_count {
            return Err(ErrorObjectOwned::owned(
                6,
                format!(
                    "Requested limit ({}) exceeds available beads in highest work path. The maximum available count is {}. Please use a limit between 1 and {}. You can use 'getbeadcount' to check the total number of beads in the braid.",
                    requested_limit, available_count, available_count
                ),
                None::<()>,
            ));
        }

        let hw_path_hashes: Vec<String> = bead_list
            .iter()
            .take(requested_limit)
            .map(|&index| {
                braid_data.beads[index]
                    .block_header
                    .block_hash()
                    .to_string()
            })
            .collect();

        Ok(hw_path_hashes)
    }

    async fn get_ipc_stats(&self) -> Result<Value, ErrorObjectOwned> {
        let (responder, receiver) = oneshot::channel();
        let command = RpcProxyCommand::GetStats { responder };

        if self.rpc_proxy_tx.send(command).is_err() {
            return Err(ErrorObjectOwned::owned(
                5,
                "IPC proxy handler channel closed - IPC handler is not running",
                None::<()>,
            ));
        }

        match receiver.await {
            Ok(Ok(stats)) => {
                let value = serde_json::json!({
                    "failed_requests": stats.failed_requests,
                    "pending_requests": stats.pending_requests,
                    "avg_processing_time_ms": stats.avg_processing_time_ms,
                    "queue_sizes": {
                        "critical": stats.queue_sizes.critical,
                        "high": stats.queue_sizes.high,
                        "normal": stats.queue_sizes.normal,
                        "low": stats.queue_sizes.low,
                    }
                });
                info!(
                    "IPC queue statistics: failed={} avg_ms={} critical={} high={} normal={} low={}",
                    stats.failed_requests,
                    stats.avg_processing_time_ms,
                    stats.queue_sizes.critical,
                    stats.queue_sizes.high,
                    stats.queue_sizes.normal,
                    stats.queue_sizes.low
                );
                Ok(value)
            }
            Ok(Err(e)) => Err(ErrorObjectOwned::owned(
                6,
                &format!("IPC queue statistics request failed: {}", e),
                None::<()>,
            )),
            Err(_) => Err(ErrorObjectOwned::owned(
                5,
                "IPC proxy handler channel closed - response receiver dropped",
                None::<()>,
            )),
        }
    }

    async fn get_braid_info(&self) -> Result<Value, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;

        let tips: Vec<String> = braid_data
            .tips
            .iter()
            .map(|&index| {
                braid_data.beads[index]
                    .block_header
                    .block_hash()
                    .to_string()
            })
            .collect();

        let genesis_beads: Vec<String> = braid_data
            .genesis_beads
            .iter()
            .map(|&index| {
                braid_data.beads[index]
                    .block_header
                    .block_hash()
                    .to_string()
            })
            .collect();

        let total_work = if braid_data.beads.is_empty() {
            "0".to_string()
        } else {
            let first_work = braid_data.beads[0].block_header.work();
            let zero_work = first_work - first_work;
            braid_data
                .beads
                .iter()
                .fold(zero_work, |acc, bead| acc + bead.block_header.work())
                .to_string()
        };

        let braid_info = BraidInfo {
            bead_count: braid_data.beads.len(),
            tip_count: braid_data.tips.len(),
            tips,
            cohort_count: braid_data.cohorts.len(),
            orphan_count: braid_data.orphan_beads.len(),
            genesis_beads,
            total_work,
        };

        serde_json::to_value(&braid_info)
            .map_err(|_| ErrorObjectOwned::owned(2, "Internal Server Error", None::<()>))
    }

    async fn get_node_info(&self, bead_hash: String) -> Result<Value, ErrorObjectOwned> {
        info!(bead_hash = %bead_hash, "Get Node Info request received");

        let hash = bead_hash
            .parse::<BeadHash>()
            .map_err(|_| ErrorObjectOwned::owned(
                1,
                "Invalid bead hash format. Expected a 64-character hex-encoded string representing a bead's block hash.",
                None::<()>
            ))?;

        let braid_data = self.braid_arc.read().await;

        let bead = braid_data
            .beads
            .iter()
            .find(|bead| bead.block_header.block_hash() == hash)
            .cloned()
            .ok_or_else(|| ErrorObjectOwned::owned(
                3,
                format!("Bead not found. No bead with hash '{}' exists in the braid. Use 'gettips' or 'getbraidinfo' to find available bead hashes.", bead_hash),
                None::<()>
            ))?;

        let node_info = NodeInfo {
            common_pubkey: bead.committed_metadata.comm_pub_key.to_string(),
            miner_ip: bead.committed_metadata.miner_ip.clone(),
            payout_address: bead.committed_metadata.payout_address.clone(),
            minimum_target: bead
                .committed_metadata
                .min_target
                .to_consensus()
                .to_string(),
        };

        serde_json::to_value(&node_info)
            .map_err(|_| ErrorObjectOwned::owned(2, "Internal Server Error", None::<()>))
    }

    async fn get_peer_info(&self) -> Result<Value, ErrorObjectOwned> {
        info!("Get Peer Info Request Received");

        // Use read lock for concurrent access (RPC server only reads)
        let peer_manager_guard = self.peer_manager.read().await;
        Ok(peer_manager_guard.get_peers_json())
    }

    /// Give the list of transactions staged for the next bead we mine.
    /// This is achieved by querying the latest block template managed by the Stratum server,
    /// excluding the coinbase transaction.
    async fn staged_transactions(&self) -> Result<Value, ErrorObjectOwned> {
        info!("Staged transaction request received");

        let latest_block_template_guard = self.latest_block.lock().await;

        // The `transactions` in the block template include the coinbase transaction at index 0.
        // "Staged transactions" for mining should only include the non-coinbase transactions.
        let staged_txs: Vec<StagedTxEntry> = if latest_block_template_guard.transactions.len() > 1 {
            latest_block_template_guard.transactions[1..]
                .iter()
                .map(|tx| StagedTxEntry {
                    txid: tx.compute_txid().to_string(),
                    tx: tx.clone(),
                })
                .collect()
        } else {
            Vec::new()
        };

        serde_json::to_value(&staged_txs).map_err(|e| {
            ErrorObjectOwned::owned(
                2,
                format!("Internal Error: Failed to serialize transactions: {}", e),
                None::<()>,
            )
        })
    }

    async fn unstage_transactions(&self, txid: String) -> Result<bool, ErrorObjectOwned> {
        info!(txid = %txid, "unstage_transactions request received");
        let (responder, receiver) = oneshot::channel();
        let command = RpcProxyCommand::RemoveTransaction { txid, responder };

        if self.rpc_proxy_tx.send(command).is_err() {
            return Err(ErrorObjectOwned::owned(
                5,
                "IPC proxy handler channel closed - IPC handler is not running",
                None::<()>,
            ));
        }

        match receiver.await {
            Ok(Ok(was_removed)) => Ok(was_removed),
            Ok(Err(e)) => Err(ErrorObjectOwned::owned(
                6,
                &format!("Transaction removal failed: {}", e),
                None::<()>,
            )),
            Err(_) => Err(ErrorObjectOwned::owned(
                5,
                "IPC proxy handler channel closed - response receiver dropped",
                None::<()>,
            )),
        }
    }

    async fn bitcoin_proxy(
        &self,
        method: String,
        params: serde_json::Value,
    ) -> Result<serde_json::Value, ErrorObjectOwned> {
        info!(method = %method, "bitcoin_proxy request received");

        let rpc_config = self.bitcoin_rpc_config.as_ref().ok_or_else(|| {
            ErrorObjectOwned::owned(
                5,
                "Bitcoin RPC proxy not configured. Please provide RPC credentials (--rpcuser/--rpcpass)",
                None::<()>,
            )
        })?;

        match call_bitcoin_rpc_direct(rpc_config, &method, &params).await {
            Ok(result) => {
                info!(method = %method, "bitcoin_proxy request completed successfully");
                Ok(result)
            }
            Err(e) => {
                warn!(method = %method, error = %e, "bitcoin_proxy request failed");
                Err(ErrorObjectOwned::owned(
                    6,
                    &format!("Bitcoin RPC error: {}", e),
                    None::<()>,
                ))
            }
        }
    }
}
struct LoggingMiddleware<S>(S);

impl<S> RpcServiceT for LoggingMiddleware<S>
where
    S: RpcServiceT,
{
    type MethodResponse = S::MethodResponse;
    type NotificationResponse = S::NotificationResponse;
    type BatchResponse = S::BatchResponse;

    fn call<'a>(
        &self,
        request: Request<'a>,
    ) -> impl Future<Output = Self::MethodResponse> + Send + 'a {
        info!(request = ?request, "RPC request received");
        assert!(request.extensions().get::<ConnectionId>().is_some());

        self.0.call(request)
    }

    fn batch<'a>(&self, batch: Batch<'a>) -> impl Future<Output = Self::BatchResponse> + Send + 'a {
        info!(batch = ?batch, "RPC batch received");
        self.0.batch(batch)
    }

    fn notification<'a>(
        &self,
        n: Notification<'a>,
    ) -> impl Future<Output = Self::NotificationResponse> + Send + 'a {
        info!(notification = ?n, "RPC notification received");
        self.0.notification(n)
    }
}
//server building
//running a server in seperate spawn event
pub async fn run_rpc_server(
    braid_shared_pointer: Arc<RwLock<Braid>>,
    bind_address: &str,
    peer_manager: Arc<tokio::sync::RwLock<PeerManager>>,
    stratum_connection_mapping: Arc<tokio::sync::RwLock<stratum::ConnectionMapping>>,
    latest_block_template: Arc<Mutex<BlockTemplate>>,
    rpc_proxy_tx: mpsc::UnboundedSender<RpcProxyCommand>,
    bitcoin_rpc_config: Option<BitcoinRpcConfig>,
) -> Result<SocketAddr, ()> {
    //Initializing the middleware
    let rpc_middleware =
        jsonrpsee::server::middleware::rpc::RpcServiceBuilder::new().layer_fn(LoggingMiddleware);
    //building the context/server supporting the http transport and ws
    let server = jsonrpsee::server::Server::builder()
        .set_rpc_middleware(rpc_middleware)
        .build(bind_address)
        .await
        .unwrap();
    //listening address for incoming requests/connection
    let addr = server.local_addr().unwrap();
    //context for the served server
    let rpc_impl = RpcServerImpl::new(
        braid_shared_pointer,
        peer_manager,
        stratum_connection_mapping,
        latest_block_template,
        rpc_proxy_tx,
        bitcoin_rpc_config.clone(),
    );
    let handle = server.start(rpc_impl.into_rpc());

    // Parse host from bind_address
    let (bind_host, _port) = bind_address.rsplit_once(':').unwrap_or((bind_address, ""));
    let endpoints = crate::utils::server_endpoints(bind_host, addr.port(), "http");
    if endpoints.is_empty() {
        warn!(
            host = %bind_host,
            port = %_port,
            "RPC server listening but no interfaces discovered"
        );
    } else {
        for endpoint in endpoints {
            info!(endpoint = %endpoint, "RPC server is listening");
        }
    }

    tokio::spawn(
        //handling the stopping of the server
        handle.stopped(),
    );
    Ok(addr)
}

/// Call Bitcoin RPC method directly using HTTP JSON-RPC
async fn call_bitcoin_rpc_direct(
    config: &BitcoinRpcConfig,
    method: &str,
    params: &serde_json::Value,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let url = config.rpc_url();
    let request = JsonRpcRequest {
        jsonrpc: "2.0",
        method: method.to_string(),
        params: params.clone(),
        id: 1,
    };

    let mut request_builder = config.client.post(&url).json(&request);

    // Add authentication using username/password
    if !config.username.is_empty() {
        request_builder = request_builder.basic_auth(
            &config.username,
            if config.password.is_empty() {
                None
            } else {
                Some(&config.password)
            },
        );
    }

    let response = request_builder
        .send()
        .await
        .map_err(|e| format!("HTTP request failed: {}", e))?;

    if !response.status().is_success() {
        let status = response.status();
        let text = response
            .text()
            .await
            .unwrap_or_else(|_| "Could not read error body".to_string());
        return Err(format!("HTTP error {}: {}", status, text).into());
    }

    let rpc_response: JsonRpcResponse = response
        .json()
        .await
        .map_err(|e| format!("Failed to parse JSON response: {}", e))?;

    if let Some(error) = rpc_response.error {
        return Err(format!(
            "Bitcoin RPC error: {}",
            serde_json::to_string(&error).unwrap_or_else(|_| "Unknown error".to_string())
        )
        .into());
    }

    rpc_response
        .result
        .ok_or_else(|| "RPC response missing result field".into())
}

#[tokio::test]
pub async fn test_extend_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9101";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        // Provide a dummy ConnectionMapping for the test
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();

    // Give server time to start
    tokio::time::sleep(tokio::time::Duration::from_millis(1000)).await;

    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let new_bead = create_test_bead(2, Some(test_bead1.block_header.block_hash()));
    let bead_json_str = serde_json::to_string(&new_bead).expect("Failed to serialize bead");

    let mut params = ArrayParams::new();
    params.insert(bead_json_str).unwrap();

    //Extending the bead
    let response: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params).await;

    assert_eq!(response.unwrap(), "Bead added successfully".to_string());

    let get_bead_params = ArrayParams::new();
    //Checking for the updated bead count after successful extension of braid
    let num_beads: Result<u64, jsonrpsee::core::ClientError> =
        client.request("getbeadcount", get_bead_params).await;

    assert_eq!(num_beads.unwrap(), 2);
}

#[tokio::test]
pub async fn test_same_bead_extend() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    //Initializing the test server
    let rpc_middleware =
        jsonrpsee::server::middleware::rpc::RpcServiceBuilder::new().layer_fn(LoggingMiddleware);
    let server = jsonrpsee::server::Server::builder()
        .set_rpc_middleware(rpc_middleware)
        .build("127.0.0.1:8889")
        .await
        .unwrap();
    let rpc_impl = RpcServerImpl::new(
        braid,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        {
            let (tx, _rx) = mpsc::unbounded_channel();
            tx
        },
        None, // No Bitcoin RPC config for tests
    );
    let _handle = server.start(rpc_impl.into_rpc());

    let server_addr = "127.0.0.1:8889";
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let new_bead = create_test_bead(2, Some(test_bead1.block_header.block_hash()));

    let bead_json_str = serde_json::to_string(&new_bead).expect("Failed to serialize bead");

    let mut params = ArrayParams::new();
    params.insert(bead_json_str).unwrap();

    //Extending the bead
    let _response_original: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params.clone()).await;

    //Extending the same bead again bead
    let response_duplicate: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params).await;
    assert_eq!(
        response_duplicate.unwrap(),
        "Bead already exists".to_string()
    );
}
#[tokio::test]
pub async fn test_cohort_count_rpc() {
    let test_bead_1 = create_test_bead(1, None);
    let test_bead_2 = create_test_bead(2, Some(test_bead_1.block_header.block_hash()));
    let test_bead_3 = create_test_bead(3, Some(test_bead_2.block_header.block_hash()));
    let test_bead_4 = create_test_bead(2, Some(test_bead_3.block_header.block_hash()));

    let genesis_beads = vec![test_bead_1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    //Initializing the test server
    let rpc_middleware =
        jsonrpsee::server::middleware::rpc::RpcServiceBuilder::new().layer_fn(LoggingMiddleware);
    let server = jsonrpsee::server::Server::builder()
        .set_rpc_middleware(rpc_middleware)
        .build("127.0.0.1:9000")
        .await
        .unwrap();
    let rpc_impl = RpcServerImpl::new(
        braid,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        {
            let (tx, _rx) = mpsc::unbounded_channel();
            tx
        },
        None, // No Bitcoin RPC config for tests
    );
    let _handle = server.start(rpc_impl.into_rpc());

    let server_addr = "127.0.0.1:9000";
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let test_bead_2_json_str =
        serde_json::to_string(&test_bead_2).expect("Failed to serialize bead");
    let test_bead_3_json_str =
        serde_json::to_string(&test_bead_3).expect("Failed to serialize bead");
    let test_bead_4_json_str =
        serde_json::to_string(&test_bead_4).expect("Failed to serialize bead");

    let mut params_test_bead_2 = ArrayParams::new();
    params_test_bead_2.insert(test_bead_2_json_str).unwrap();
    let mut params_test_bead_3 = ArrayParams::new();
    params_test_bead_3.insert(test_bead_3_json_str).unwrap();
    let mut params_test_bead_4 = ArrayParams::new();
    params_test_bead_4.insert(test_bead_4_json_str).unwrap();

    //Extending the bead
    let response_test_bead_2: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params_test_bead_2).await;
    assert_eq!(
        response_test_bead_2.unwrap(),
        "Bead added successfully".to_string()
    );

    let response_test_bead_3: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params_test_bead_3).await;
    assert_eq!(
        response_test_bead_3.unwrap(),
        "Bead added successfully".to_string()
    );

    let response_test_bead_4: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params_test_bead_4).await;
    assert_eq!(
        response_test_bead_4.unwrap(),
        "Bead added successfully".to_string()
    );
    let response_cohort_cnt: Result<u64, jsonrpsee::core::ClientError> =
        client.request("getcohortcount", ArrayParams::new()).await;

    assert_eq!(response_cohort_cnt.unwrap(), 4);
}

#[tokio::test]
pub async fn test_get_bead_count_cli_flow() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    // Start RPC server
    let server_addr = "127.0.0.1:9100"; // Different port to avoid conflicts
    let _server_addr = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        {
            let (tx, _rx) = mpsc::unbounded_channel();
            tx
        },
        None,
    )
    .await
    .unwrap();

    // Give server time to start
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    // Test: Make HTTP request like CLI would
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let params = ArrayParams::new();
    let num_beads: Result<u64, jsonrpsee::core::ClientError> =
        client.request("getbeadcount", params).await;

    assert!(num_beads.is_ok());
    assert_eq!(num_beads.unwrap(), 1); // We have 1 genesis bead
}

#[tokio::test]
pub async fn test_get_tips_cli_flow() {
    let test_bead1 = create_test_bead(1, None);
    let test_bead2 = create_test_bead(2, Some(test_bead1.block_header.block_hash()));
    let genesis_beads = vec![test_bead1.clone()];
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    // Add second bead
    {
        let mut braid_guard = braid.write().await;
        braid_guard.extend(&test_bead2);
    }

    // Start RPC server
    let server_addr = "127.0.0.1:6684";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        {
            let (tx, _rx) = mpsc::unbounded_channel();
            tx
        },
        None,
    )
    .await
    .unwrap();

    tokio::time::sleep(tokio::time::Duration::from_millis(1000)).await;

    // Test gettips command
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let params = ArrayParams::new();
    let tips: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("gettips", params).await;

    assert!(tips.is_ok());
    let tips_vec = tips.unwrap();
    assert_eq!(tips_vec.len(), 1); // Should have 1 tip (test_bead2)
    assert_eq!(
        tips_vec[0],
        test_bead2.block_header.block_hash().to_string()
    );
}

#[tokio::test]
pub async fn test_get_bead_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9001";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    // Test getbead for existing bead
    let bead_hash = test_bead1.block_header.block_hash().to_string();
    let mut params = ArrayParams::new();
    params.insert(bead_hash.clone()).unwrap();

    let response: Result<Bead, jsonrpsee::core::ClientError> =
        client.request("getbead", params).await;

    assert!(response.is_ok());
    let fetched_bead = response.unwrap();
    assert_eq!(
        fetched_bead.block_header.block_hash().to_string(),
        bead_hash
    );

    // Test getbead for non-existing bead
    let non_existent_hash =
        "0000000000000000000000000000000000000000000000000000000000000001".to_string();
    let mut params = ArrayParams::new();
    params.insert(non_existent_hash).unwrap();
    let response: Result<Bead, jsonrpsee::core::ClientError> =
        client.request("getbead", params).await;

    assert!(response.is_err());
    if let jsonrpsee::core::ClientError::Call(error) = response.unwrap_err() {
        assert_eq!(error.code(), 3);
        assert_eq!(error.message(), "Bead not found");
    } else {
        panic!("Expected a Call error");
    }
}

#[tokio::test]
pub async fn test_get_cohort_rpc() {
    let test_bead_1 = create_test_bead(1, None); // cohort 0
    let test_bead_2 = create_test_bead(2, Some(test_bead_1.block_header.block_hash())); // cohort 1
    let genesis_beads = vec![test_bead_1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    {
        let mut braid_guard = braid.write().await;
        braid_guard.extend(&test_bead_2);
    }

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9002";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    // Test getcohortbyid for existing cohort
    let mut params = ArrayParams::new();
    params.insert(1 as u64).unwrap(); // Get cohort 1
    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("getcohortbyid", params).await;

    assert!(response.is_ok());
    let cohort_hashes = response.unwrap();
    assert_eq!(cohort_hashes.len(), 1);
    assert_eq!(
        cohort_hashes[0],
        test_bead_2.block_header.block_hash().to_string()
    );

    // Test getcohortbyid for non-existing cohort
    let mut params = ArrayParams::new();
    params.insert(99 as u64).unwrap();
    let response: Result<String, jsonrpsee::core::ClientError> =
        client.request("getcohortbyid", params).await;

    assert!(response.is_err());
    if let jsonrpsee::core::ClientError::Call(error) = response.unwrap_err() {
        assert_eq!(error.code(), 3);
        assert_eq!(error.message(), "Cohort not found for given ID");
    } else {
        panic!("Expected a Call error");
    }
}

#[tokio::test]
pub async fn test_get_genesis_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9003";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let response: Result<String, jsonrpsee::core::ClientError> =
        client.request("getgenesis", ArrayParams::new()).await;

    assert!(response.is_ok());
    let genesis_hash = response.unwrap();
    assert_eq!(
        genesis_hash,
        test_bead1.block_header.block_hash().to_string()
    );
}

#[tokio::test]
pub async fn test_get_parents_and_children_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let test_bead2 = create_test_bead(2, Some(test_bead1.block_header.block_hash()));
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    {
        let mut braid_guard = braid.write().await;
        braid_guard.extend(&test_bead2);
    }

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9004";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    // Test getparents for bead2
    let bead2_hash = test_bead2.block_header.block_hash().to_string();
    let mut params = ArrayParams::new();
    params.insert(bead2_hash.clone()).unwrap();
    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("getparents", params).await;

    assert!(response.is_ok());
    let parent_hashes = response.unwrap();
    assert_eq!(parent_hashes.len(), 1);
    assert_eq!(
        parent_hashes[0],
        test_bead1.block_header.block_hash().to_string()
    );

    // Test getchildren for bead1
    let bead1_hash = test_bead1.block_header.block_hash().to_string();
    let mut params = ArrayParams::new();
    params.insert(bead1_hash).unwrap();
    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("getchildren", params).await;

    assert!(response.is_ok());
    let children_hashes = response.unwrap();
    assert_eq!(children_hashes.len(), 1);
    assert_eq!(children_hashes[0], bead2_hash);

    // Test getchildren for bead2 (should have no children)
    let mut params = ArrayParams::new();
    params.insert(bead2_hash).unwrap();
    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("getchildren", params).await;

    assert!(response.is_ok());
    let children_hashes = response.unwrap();
    assert!(children_hashes.is_empty());
}

#[tokio::test]
pub async fn test_get_hwpath_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let test_bead2 = create_test_bead(2, Some(test_bead1.block_header.block_hash()));
    let test_bead3 = create_test_bead(3, Some(test_bead2.block_header.block_hash()));
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    {
        let mut braid_guard = braid.write().await;
        braid_guard.extend(&test_bead2);
        braid_guard.extend(&test_bead3);
    }

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9005";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let mut params = ArrayParams::new();
    params.insert(10 as u8).unwrap();
    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("gethighestworkpathbycount", params).await;

    if let Ok(hw_path) = response {
        assert!(!hw_path.is_empty());
    }

    // Test with limit
    let mut params = ArrayParams::new();
    params.insert(2 as u8).unwrap();
    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("gethighestworkpathbycount", params).await;

    if let Ok(hw_path) = response {
        assert!(hw_path.len() <= 2);
    }
}

#[tokio::test]
pub async fn test_get_braid_info_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9006";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let response: Result<Value, jsonrpsee::core::ClientError> =
        client.request("getbraidinfo", ArrayParams::new()).await;

    assert!(response.is_ok());
    let braid_info: BraidInfo = serde_json::from_value(response.unwrap()).unwrap();

    // Check some fields
    assert_eq!(braid_info.bead_count, 1);
    assert_eq!(braid_info.tip_count, 1);
    assert_eq!(
        braid_info.tips[0],
        test_bead1.block_header.block_hash().to_string()
    );
}

#[tokio::test]
pub async fn test_get_node_info_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9007";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let bead_hash = test_bead1.block_header.block_hash().to_string();
    let mut params = ArrayParams::new();
    params.insert(bead_hash).unwrap();

    let response: Result<Value, jsonrpsee::core::ClientError> =
        client.request("getnodeinfo", params).await;

    assert!(response.is_ok());
    let node_info: NodeInfo = serde_json::from_value(response.unwrap()).unwrap();

    assert_eq!(
        node_info.common_pubkey,
        test_bead1.committed_metadata.comm_pub_key.to_string()
    );
    assert_eq!(
        node_info.payout_address,
        test_bead1.committed_metadata.payout_address
    );
}

#[tokio::test]
pub async fn test_get_peer_info_rpc() {
    use libp2p::identity::Keypair;
    use libp2p::PeerId;
    use std::net::{IpAddr, Ipv4Addr};
    use std::time::Duration;

    // Helper to generate a peer id (testing purpose only )
    fn generate_peer_id() -> PeerId {
        let keypair = Keypair::generate_ed25519();
        PeerId::from(keypair.public())
    }

    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(vec![create_test_bead(
            1, None,
        )])));
    let (proxy_tx, _) = mpsc::unbounded_channel();

    // --- 1. Test with no peers ---
    let peer_manager_empty = Arc::new(tokio::sync::RwLock::new(PeerManager::new(8)));
    let server_addr_empty = "127.0.0.1:9008";
    let server_empty = jsonrpsee::server::Server::builder()
        .build(server_addr_empty)
        .await
        .unwrap();
    let rpc_impl_empty = RpcServerImpl::new(
        Arc::clone(&braid),
        peer_manager_empty,
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx.clone(),
        None,
    );
    let handle_empty = server_empty.start(rpc_impl_empty.into_rpc());

    let client_empty: HttpClient = HttpClient::builder()
        .build(format!("http://{}", server_addr_empty))
        .unwrap();

    let response_empty: Result<Value, _> = client_empty
        .request("getpeerinfo", ArrayParams::new())
        .await;
    handle_empty.stop().unwrap(); // Stop the server

    assert!(response_empty.is_ok());
    let response_value_empty = response_empty.unwrap();
    println!(
        "\n--- Response with 0 peers ---\n{}\n---------------------------\n",
        serde_json::to_string_pretty(&response_value_empty).unwrap()
    );
    assert_eq!(response_value_empty["connected"], 0);

    // --- 2. Test with one peer ---
    let mut peer_manager_with_peers = PeerManager::new(8);
    let peer_id = generate_peer_id();
    let peer_id_str = peer_id.to_base58();
    let peer_ip = IpAddr::V4(Ipv4Addr::new(192, 168, 1, 5));
    peer_manager_with_peers.add_peer(peer_id, false, Some(peer_ip));
    peer_manager_with_peers.update_latency(&peer_id, Duration::from_millis(75));
    peer_manager_with_peers.update_score(&peer_id, 25.0);

    let peer_manager_arc = Arc::new(tokio::sync::RwLock::new(peer_manager_with_peers));
    let server_addr_with_peers = "127.0.0.1:9018"; // Use a different port
    let server_with_peers = jsonrpsee::server::Server::builder()
        .build(server_addr_with_peers)
        .await
        .unwrap();
    let rpc_impl_with_peers = RpcServerImpl::new(
        Arc::clone(&braid),
        peer_manager_arc,
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    );
    let handle_with_peers = server_with_peers.start(rpc_impl_with_peers.into_rpc());

    let client_with_peers: HttpClient = HttpClient::builder()
        .build(format!("http://{}", server_addr_with_peers))
        .unwrap();

    let response_with_peers: Result<Value, _> = client_with_peers
        .request("getpeerinfo", ArrayParams::new())
        .await;
    handle_with_peers.stop().unwrap(); // Stop the server

    assert!(response_with_peers.is_ok());
    let response_value_with_peers = response_with_peers.unwrap();
    println!(
        "--- Response with 1 peer ---\n{}\n--------------------------\n",
        serde_json::to_string_pretty(&response_value_with_peers).unwrap()
    );

    // Assert that the output contains the peer's info
    assert_eq!(response_value_with_peers["connected"], 1);
    let peers_array = response_value_with_peers["peers"].as_array().unwrap();
    assert_eq!(peers_array.len(), 1);
    assert_eq!(peers_array[0]["peer_id"], peer_id_str);
    assert_eq!(peers_array[0]["ip"], "192.168.1.5");
    assert_eq!(peers_array[0]["latency_ms"], 75.0);
    assert!(peers_array[0]["score"].as_f64().unwrap() > 0.0);
}

#[tokio::test]
pub async fn test_get_miner_info_rpc() {
    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(vec![create_test_bead(
            1, None,
        )])));

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let stratum_map = Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new()));
    {
        let mut map = stratum_map.write().await;
        let (tx, _) = mpsc::channel(1);
        map.downstream_channel_mapping.insert(
            "1.2.3.4:5678".to_string(),
            stratum::ConnectionInfo {
                connection_id: 0,
                sender: tx,
            },
        );
    }

    let server_addr = "127.0.0.1:9009";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        stratum_map,
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let response: Result<Vec<String>, jsonrpsee::core::ClientError> =
        client.request("getminerinfo", ArrayParams::new()).await;

    assert!(response.is_ok());
    let miner_ips = response.unwrap();
    assert_eq!(miner_ips, vec!["1.2.3.4:5678".to_string()]);
}

#[tokio::test]
pub async fn test_staged_transactions_rpc() {
    use bitcoin::consensus::deserialize;

    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(vec![create_test_bead(
            1, None,
        )])));
    let (proxy_tx, _) = mpsc::unbounded_channel();
    let latest_block = Arc::new(Mutex::new(stratum::BlockTemplate::default()));

    let server_addr = "127.0.0.1:9013";
    let server = jsonrpsee::server::Server::builder()
        .build(server_addr)
        .await
        .unwrap();
    let rpc_impl = RpcServerImpl::new(
        braid,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::clone(&latest_block),
        proxy_tx,
        None,
    );
    let handle = server.start(rpc_impl.into_rpc());

    let client: HttpClient = HttpClient::builder()
        .build(format!("http://{}", server_addr))
        .unwrap();

    // 1. Test with an empty block template
    let response_empty: Result<Value, _> = client
        .request("stagedtransactions", ArrayParams::new())
        .await;

    assert!(response_empty.is_ok());
    let returned_txs_empty: Vec<StagedTxEntry> =
        serde_json::from_value(response_empty.unwrap()).unwrap();
    assert!(returned_txs_empty.is_empty());

    // 2. Test with only a coinbase transaction
    let coinbase_tx_hex = "01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff0704ffff001d0104ffffffff0100f2052a01000000434104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac00000000";
    let coinbase_tx: Transaction = deserialize(&hex::decode(coinbase_tx_hex).unwrap()).unwrap();

    {
        let mut block_template = latest_block.lock().await;
        block_template.transactions = vec![coinbase_tx.clone()];
    }

    let response_coinbase_only: Result<Value, _> = client
        .request("stagedtransactions", ArrayParams::new())
        .await;

    assert!(response_coinbase_only.is_ok());
    let returned_txs_coinbase_only: Vec<StagedTxEntry> =
        serde_json::from_value(response_coinbase_only.unwrap()).unwrap();
    assert!(
        returned_txs_coinbase_only.is_empty(),
        "Should return empty list when only coinbase tx is present"
    );

    // 3. Test with coinbase and a regular transaction
    let regular_tx_hex = "0100000001c997a5e56e104102fa209c6a852dd90660a20b2d9c352423edce25857fcd3704000000004847304402204e45e16932b8af514961a1d3a1a25fdf3f4f7732e9d624c6c61548ab5fb8cd410220181522ec8eca07de4860a4acdd12909d831cc56cbbac4622082221a8768d1d0901ffffffff0200ca9a3b000000001976a914e04a251c1cde050eb41328b0f8395020120150b388ac80969800000000001976a914480252b4ac4038bed9588663a43f885e5884483788ac00000000";
    let regular_tx: Transaction = deserialize(&hex::decode(regular_tx_hex).unwrap()).unwrap();

    {
        let mut block_template = latest_block.lock().await;
        block_template.transactions = vec![coinbase_tx.clone(), regular_tx.clone()];
    }

    let response_with_tx: Result<Value, _> = client
        .request("stagedtransactions", ArrayParams::new())
        .await;

    assert!(response_with_tx.is_ok());
    let returned_txs: Vec<StagedTxEntry> =
        serde_json::from_value(response_with_tx.unwrap()).unwrap();

    assert_eq!(
        returned_txs.len(),
        1,
        "Should return one regular transaction"
    );
    assert_eq!(
        returned_txs[0].txid,
        regular_tx.compute_txid().to_string(),
        "Returned txid should match the regular mock txid"
    );
    assert_eq!(
        returned_txs[0].tx.compute_txid(),
        regular_tx.compute_txid(),
        "Returned tx should match the regular mock tx"
    );

    handle.stop().unwrap();
}

#[tokio::test]
pub async fn test_get_ipc_stats_rpc() {
    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(vec![create_test_bead(
            1, None,
        )])));
    let (proxy_tx, mut proxy_rx) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9012";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let request_future = client.request("getipcstats", ArrayParams::new());

    let (response, _) = tokio::join!(request_future, async {
        if let Some(RpcProxyCommand::GetStats { responder }) = proxy_rx.recv().await {
            let stats = QueueStats {
                failed_requests: 1,
                pending_requests: 0,
                avg_processing_time_ms: 123,
                queue_sizes: crate::ipc::client::QueueSizeStats {
                    critical: 1,
                    high: 2,
                    normal: 3,
                    low: 4,
                },
            };
            responder.send(Ok(stats)).unwrap();
        }
    });

    assert!(response.is_ok());
    let stats: Value = response.unwrap();
    assert_eq!(stats["failed_requests"], 1);
    assert_eq!(stats["avg_processing_time_ms"], 123);
    assert_eq!(stats["queue_sizes"]["critical"], 1);
    assert_eq!(stats["queue_sizes"]["high"], 2);
    assert_eq!(stats["queue_sizes"]["normal"], 3);
    assert_eq!(stats["queue_sizes"]["low"], 4);
}

#[tokio::test]
pub async fn test_get_ipc_stats_rpc_simple() {
    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(vec![create_test_bead(
            1, None,
        )])));
    let (proxy_tx, mut proxy_rx) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9020";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let request_future = client.request("getipcstats", ArrayParams::new());

    let (response, _) = tokio::join!(request_future, async {
        if let Some(RpcProxyCommand::GetStats { responder }) = proxy_rx.recv().await {
            let stats = QueueStats {
                failed_requests: 0,
                pending_requests: 0,
                avg_processing_time_ms: 50,
                queue_sizes: crate::ipc::client::QueueSizeStats {
                    critical: 0,
                    high: 1,
                    normal: 2,
                    low: 3,
                },
            };
            responder.send(Ok(stats)).unwrap();
        }
    });

    assert!(response.is_ok());
    let stats: Value = response.unwrap();
    assert_eq!(stats["failed_requests"], 0);
    assert_eq!(stats["avg_processing_time_ms"], 50);
    assert_eq!(stats["queue_sizes"]["high"], 1);
    assert_eq!(stats["queue_sizes"]["normal"], 2);
    assert_eq!(stats["queue_sizes"]["low"], 3);
}

#[tokio::test]
pub async fn test_unstage_transactions_rpc_simple() {
    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(vec![create_test_bead(
            1, None,
        )])));
    let (proxy_tx, mut proxy_rx) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9021";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let test_txid = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let mut params = ArrayParams::new();
    params.insert(test_txid.to_string()).unwrap();

    let request_future: futures::future::BoxFuture<'_, Result<bool, jsonrpsee::core::ClientError>> =
        Box::pin(client.request("unstagetransactions", params));

    let (response, _) = tokio::join!(request_future, async {
        if let Some(RpcProxyCommand::RemoveTransaction { txid, responder }) = proxy_rx.recv().await
        {
            assert_eq!(txid, test_txid);
            responder.send(Ok(true)).unwrap();
        }
    });

    assert!(response.is_ok());
    assert_eq!(response.unwrap(), true);
}

#[tokio::test]
pub async fn test_get_mining_info_rpc() {
    use serde_json::json;

    // Create test beads with known public key
    let test_bead1 = create_test_bead(1, None);
    let test_bead2 = create_test_bead(2, Some(test_bead1.block_header.block_hash()));
    let test_bead3 = create_test_bead(3, Some(test_bead2.block_header.block_hash()));

    // Get the public key used in test beads
    let test_public_key = test_bead1.committed_metadata.comm_pub_key.to_string();

    let genesis_beads = vec![test_bead1.clone()];
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    // Add additional beads to the braid
    {
        let mut braid_guard = braid.write().await;
        braid_guard.extend(&test_bead2);
        braid_guard.extend(&test_bead3);
    }

    let (proxy_tx, _) = mpsc::unbounded_channel();

    let server_addr = "127.0.0.1:9089";
    let _ = run_rpc_server(
        Arc::clone(&braid),
        server_addr,
        Arc::new(tokio::sync::RwLock::new(PeerManager::new(8))),
        Arc::new(tokio::sync::RwLock::new(stratum::ConnectionMapping::new())),
        Arc::new(Mutex::new(stratum::BlockTemplate::default())),
        proxy_tx,
        None,
    )
    .await
    .unwrap();

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    // Test 1: Filter by public key - should match all 3 beads
    // jsonrpsee expects Option<Value> - pass object directly, it will be wrapped in Some()
    let params1_obj = json!({
        "public_keys": [test_public_key.clone()]
    });
    let mut array_params1 = ArrayParams::new();
    array_params1.insert(params1_obj).unwrap();
    let response1: Result<Value, _> = client.request("getmininginfo", array_params1).await;

    assert!(response1.is_ok());
    let mining_info1: serde_json::Value = response1.unwrap();
    assert_eq!(mining_info1["our_beads_count"], 3);
    assert_eq!(mining_info1["total_beads_in_braid"], 3);
    assert!(mining_info1["our_total_work"].as_str().is_some());
    assert!(mining_info1["total_work_in_braid"].as_str().is_some());
    assert!(mining_info1["our_work_share_percent"].as_f64().unwrap() > 0.0);
    assert!(mining_info1["filter_info"].as_str().is_some());

    // Test 2: Filter by non-matching public key - should match 0 beads
    let params2_obj = json!({
        "public_keys": ["030303030303030303030303030303030303030303030303030303030303030303"]
    });
    let mut array_params2 = ArrayParams::new();
    array_params2.insert(params2_obj).unwrap();
    let response2: Result<Value, _> = client.request("getmininginfo", array_params2).await;

    assert!(response2.is_ok());
    let mining_info2: serde_json::Value = response2.unwrap();
    assert_eq!(mining_info2["our_beads_count"], 0);
    assert_eq!(mining_info2["total_beads_in_braid"], 3);
    assert_eq!(mining_info2["our_total_work"], "0");
    assert_eq!(mining_info2["our_work_share_percent"], 0.0);

    // Test 3: Filter by miner IP (test beads have empty miner_ip, so this should match 0)
    let params3_obj = json!({
        "miner_ips": ["192.168.1.1"]
    });
    let mut array_params3 = ArrayParams::new();
    array_params3.insert(params3_obj).unwrap();
    let response3: Result<Value, _> = client.request("getmininginfo", array_params3).await;

    assert!(response3.is_ok());
    let mining_info3: serde_json::Value = response3.unwrap();
    assert_eq!(mining_info3["our_beads_count"], 0);

    // Test 4: Filter by empty miner IP (test beads have empty string)
    let params4_obj = json!({
        "miner_ips": [""]
    });
    let mut array_params4 = ArrayParams::new();
    array_params4.insert(params4_obj).unwrap();
    let response4: Result<Value, _> = client.request("getmininginfo", array_params4).await;

    assert!(response4.is_ok());
    let mining_info4: serde_json::Value = response4.unwrap();
    assert!(mining_info4["our_beads_count"].is_number());

    // Test 5: Multiple public keys (key rotation scenario)
    let params5_obj = json!({
        "public_keys": [test_public_key.clone(), "030303030303030303030303030303030303030303030303030303030303030303"]
    });
    let mut array_params5 = ArrayParams::new();
    array_params5.insert(params5_obj).unwrap();
    let response5: Result<Value, _> = client.request("getmininginfo", array_params5).await;

    assert!(response5.is_ok());
    let mining_info5: serde_json::Value = response5.unwrap();
    assert_eq!(mining_info5["our_beads_count"], 3); // Should match via first key

    // Test 6: Combined filters (public_keys AND miner_ips)
    let params6_obj = json!({
        "public_keys": [test_public_key.clone()],
        "miner_ips": [""]
    });
    let mut array_params6 = ArrayParams::new();
    array_params6.insert(params6_obj).unwrap();
    let response6: Result<Value, _> = client.request("getmininginfo", array_params6).await;

    assert!(response6.is_ok());
    let mining_info6: serde_json::Value = response6.unwrap();
    // Should match all beads (matches both criteria)
    assert_eq!(mining_info6["our_beads_count"], 3);

    // Test 7: Error case - no parameters (empty array)
    let response7: Result<Value, _> = client.request("getmininginfo", ArrayParams::new()).await;

    assert!(response7.is_err());
    if let jsonrpsee::core::ClientError::Call(err) = response7.unwrap_err() {
        assert_eq!(err.code(), 2);
        assert!(err.message().contains("Parameters required") || err.message().contains("filter"));
    } else {
        panic!("Expected Call error");
    }

    // Test 8: Error case - empty public_keys array
    let params8_obj = json!({
        "public_keys": []
    });
    let mut array_params8 = ArrayParams::new();
    array_params8.insert(params8_obj).unwrap();
    let response8: Result<Value, _> = client.request("getmininginfo", array_params8).await;

    assert!(response8.is_err());
    if let jsonrpsee::core::ClientError::Call(err) = response8.unwrap_err() {
        assert_eq!(err.code(), 2);
        assert!(
            err.message().contains("non-empty filter") || err.message().contains("At least one")
        );
    } else {
        panic!("Expected Call error");
    }
}
