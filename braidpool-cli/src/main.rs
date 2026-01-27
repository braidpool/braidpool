use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use serde_json::json;

/// Braidpool CLI - Command line interface for interacting with Braidpool node
#[derive(Parser, Debug)]
#[command(name = "braidpool-cli", version, about, long_about = None)]
struct Cli {
    /// RPC server URL (default: http://127.0.0.1:6682)
    #[arg(long, default_value = "http://127.0.0.1:6682")]
    rpc_url: String,

    #[command(subcommand)]
    commands: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Get a bead by hash
    #[command(name = "getbead")]
    GetBead {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Add a bead via serialized JSON string
    #[command(name = "addbead")]
    AddBead {
        /// JSON-formatted bead
        bead_data: String,
    },

    /// Get total number of beads
    #[command(name = "getbeadcount")]
    GetBeadCount,

    /// Get total number of cohorts
    #[command(name = "getcohortcount")]
    GetCohortCount,

    /// Get current DAG tips
    #[command(name = "gettips")]
    GetTips,

    /// Get a list of bead hashes in a cohort by its ID
    #[command(name = "getcohortbyid")]
    GetCohortById {
        /// The ID of the cohort
        cohort_id: u64,
    },

    /// Get the genesis bead hash for this epoch
    #[command(name = "getgenesis")]
    GetGenesis,

    /// Get a list of connected Stratum miners
    #[command(name = "getminerinfo")]
    GetMinerInfo,

    /// Get detailed statistics about beads mined by us, expected payout, etc.
    /// Requires at least one filter: public_keys or miner_ips
    #[command(name = "getmininginfo")]
    GetMiningInfo {
        /// List of public keys (hex-encoded) to filter beads by.
        /// Supports multiple keys for key rotation scenarios.
        /// Example: --public_keys "0202...,0303..."
        #[arg(long, value_delimiter = ',')]
        public_keys: Option<Vec<String>>,

        /// List of miner IP addresses to filter beads by.
        /// Useful for pool operators tracking specific miners.
        /// Example: --miner_ips "192.168.1.1,192.168.1.2"
        #[arg(long, value_delimiter = ',')]
        miner_ips: Option<Vec<String>>,
    },

    /// Get the parent hashes of a bead by bead_hash
    #[command(name = "getparents")]
    GetParents {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Get the children hashes of a bead by bead hash
    #[command(name = "getchildren")]
    GetChildren {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Get the list of beads in the highest work path, limited by count
    #[command(name = "gethighestworkpathbycount")]
    GetHighestWorkPathByCount {
        /// Limit the number of results returned
        limit: u8,
    },

    /// Get statistics about the IPC connection
    #[command(name = "getipcstats")]
    GetIpcStats,

    /// Get braid information (returns bead_count , tip_count , tips, cohort_count, orphan_count, genesis_beads, total_work)
    #[command(name = "getbraidinfo")]
    GetBraidInfo,

    /// Get node information for the node that created a specific bead
    /// Returns information about the node that created the specified bead, including:
    /// common_pubkey (libp2p public key), miner_ip, payout_address, and minimum_target.
    #[command(name = "getnodeinfo")]
    GetNodeInfo {
        /// The bead hash (block hash) as a 64-character hex-encoded string representing the bead's block hash
        /// This identifies which bead's creator node information you want to retrieve
        bead_hash: String,
    },

    /// Get peer information (IP/PeerID/libp2p address of connected peers)
    #[command(name = "getpeerinfo")]
    GetPeerInfo,

    /// Get the list of transactions staged for the next bead we mine
    #[command(name = "stagedtransactions")]
    StagedTransactions,

    /// Remove a transaction from our stage list by txid
    #[command(name = "unstagetransactions")]
    UnstageTransactions {
        /// Transaction ID to remove
        tx_id: String,
    },

    /// Proxy a Bitcoin RPC call to bitcoind
    /// Example: braidpool-cli bitcoin getblockchaininfo
    #[command(name = "bitcoin")]
    Bitcoin {
        /// Bitcoin RPC method name (e.g., "getblockchaininfo", "getblockhash", etc.)
        method: String,
        /// JSON array of parameters (optional, defaults to empty array)
        #[arg(long, default_value = "[]")]
        params: String,
    },
}

#[derive(Serialize, Debug)]
struct JsonRpcRequest {
    jsonrpc: &'static str,
    method: String,
    params: serde_json::Value,
    id: u64,
}

#[derive(Deserialize, Debug, Clone)]
pub struct JsonRpcError {
    pub code: i32,
    pub message: String,
    #[serde(default)]
    pub data: Option<serde_json::Value>,
}

impl std::fmt::Display for JsonRpcError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error {}: {}", self.code, self.message)
    }
}

impl std::error::Error for JsonRpcError {}

#[derive(Deserialize, Debug)]
#[allow(dead_code)]
struct JsonRpcResponse {
    #[serde(default)]
    jsonrpc: Option<String>,
    #[serde(default)]
    result: Option<serde_json::Value>,
    #[serde(default)]
    error: Option<JsonRpcError>,
    #[serde(default)]
    id: Option<serde_json::Value>,
}

#[derive(Debug)]
pub enum RpcCallError {
    HttpError(String),
    InvalidJson { body: String, parse_error: String },
    JsonRpcError(JsonRpcError),
    InvalidResponse(String),
}

impl std::fmt::Display for RpcCallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RpcCallError::HttpError(msg) => write!(f, "Connection error: {}", msg),
            RpcCallError::InvalidJson { body, parse_error } => {
                let truncated_body = if body.len() > 500 {
                    format!("{}... (truncated)", &body[..500])
                } else {
                    body.clone()
                };
                write!(
                    f,
                    "Invalid server response (not valid JSON): {}\nServer response: {}",
                    parse_error, truncated_body
                )
            }
            RpcCallError::JsonRpcError(err) => write!(f, "{}", err),
            RpcCallError::InvalidResponse(msg) => write!(f, "Invalid JSON-RPC response: {}", msg),
        }
    }
}

impl std::error::Error for RpcCallError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            RpcCallError::JsonRpcError(err) => Some(err),
            _ => None,
        }
    }
}

async fn call_rpc(
    client: &reqwest::Client,
    rpc_url: &str,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value, RpcCallError> {
    let rpc_request = JsonRpcRequest {
        jsonrpc: "2.0",
        method: method.to_string(),
        params,
        id: 1,
    };

    let res = client
        .post(rpc_url)
        .json(&rpc_request)
        .send()
        .await
        .map_err(|e| RpcCallError::HttpError(e.to_string()))?;

    let body_text = res
        .text()
        .await
        .map_err(|e| RpcCallError::HttpError(format!("Failed to read response body: {}", e)))?;

    match serde_json::from_str::<JsonRpcResponse>(&body_text) {
        Ok(rpc_response) => {
            if let Some(error) = rpc_response.error {
                return Err(RpcCallError::JsonRpcError(error));
            }
            if let Some(result) = rpc_response.result {
                return Ok(result);
            }
            Err(RpcCallError::InvalidResponse(
                "Response contains neither 'result' nor 'error' field".to_string(),
            ))
        }
        Err(parse_err) => Err(RpcCallError::InvalidJson {
            body: body_text,
            parse_error: parse_err.to_string(),
        }),
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(30))
        .build()?;

    let (method, params) = match &cli.commands {
        Commands::GetBead { bead_hash } => ("getbead", json!([bead_hash])),
        Commands::AddBead { bead_data } => ("addbead", json!([bead_data])),
        Commands::GetBeadCount => ("getbeadcount", json!([])),
        Commands::GetCohortCount => ("getcohortcount", json!([])),
        Commands::GetTips => ("gettips", json!([])),
        Commands::GetCohortById { cohort_id } => ("getcohortbyid", json!([cohort_id])),
        Commands::GetGenesis => ("getgenesis", json!([])),
        Commands::GetMinerInfo => ("getminerinfo", json!([])),
        Commands::GetMiningInfo {
            public_keys,
            miner_ips,
        } => {
            let mut params_obj = serde_json::Map::new();

            if let Some(keys) = public_keys {
                if !keys.is_empty() {
                    params_obj.insert(
                        "public_keys".to_string(),
                        json!(keys
                            .iter()
                            .map(|k| k.trim().to_string())
                            .collect::<Vec<_>>()),
                    );
                }
            }

            if let Some(ips) = miner_ips {
                if !ips.is_empty() {
                    params_obj.insert(
                        "miner_ips".to_string(),
                        json!(ips
                            .iter()
                            .map(|ip| ip.trim().to_string())
                            .collect::<Vec<_>>()),
                    );
                }
            }

            ("getmininginfo", json!([params_obj]))
        }
        Commands::GetParents { bead_hash } => ("getparents", json!([bead_hash])),
        Commands::GetChildren { bead_hash } => ("getchildren", json!([bead_hash])),
        Commands::GetHighestWorkPathByCount { limit } => {
            ("gethighestworkpathbycount", json!([limit]))
        }
        Commands::GetIpcStats => ("getipcstats", json!([])),
        Commands::GetBraidInfo => ("getbraidinfo", json!([])),
        Commands::GetNodeInfo { bead_hash } => ("getnodeinfo", json!([bead_hash])),
        Commands::GetPeerInfo => ("getpeerinfo", json!([])),
        Commands::StagedTransactions => ("stagedtransactions", json!([])),
        Commands::UnstageTransactions { tx_id } => ("unstagetransactions", json!([tx_id])),
        Commands::Bitcoin { method, params } => {
            let params_value: serde_json::Value =
                serde_json::from_str(params).unwrap_or_else(|_| json!([]));
            ("bitcoinproxy", json!([method, params_value]))
        }
    };

    match call_rpc(&client, &cli.rpc_url, method, params).await {
        Ok(result) => {
            let pretty_response = serde_json::to_string_pretty(&result).map_err(|e| {
                Box::new(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("Failed to serialize response: {}", e),
                ))
            })?;
            println!("{}", pretty_response);
            Ok(())
        }
        Err(e) => {
            // Print error to stderr with proper formatting
            eprintln!("Error: {}", e);

            // For JSON-RPC errors, provide additional context if available
            if let RpcCallError::JsonRpcError(ref json_err) = e {
                if let Some(ref data) = json_err.data {
                    eprintln!("\nAdditional error details:");
                    if let Ok(pretty_data) = serde_json::to_string_pretty(data) {
                        eprintln!("{}", pretty_data);
                    } else {
                        eprintln!("{:?}", data);
                    }
                }
            }

            std::process::exit(1);
        }
    }
}
