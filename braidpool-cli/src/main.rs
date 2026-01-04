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
#[command(rename_all = "PascalCase")]
enum Commands {
    /// Get a bead by hash
    GetBead {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Add a bead via serialized JSON string
    AddBead {
        /// JSON-formatted bead
        bead_data: String,
    },

    /// Get total number of beads
    GetBeadCount,

    /// Get total number of cohorts
    GetCohortCount,

    /// Get current DAG tips
    GetTips,

    /// Get a list of bead hashes in the cohort
    GetCohort {
        /// The id of the Cohort
        cohort_id: u64,
    },

    /// Get the genesis bead hash for this epoch
    GetGenesis,

    /// Get a list of connected Stratum miners
    GetMinerInfo,

    /// Get detailed statistics about a specific miner identified by connection_id/extraonce1.
    GetMiner { connection_id: u64 },
    ///  get detailed statistics about beads mined by us, expected payout, etc.
    GetMiningInfo,

    /// Get the parent hashes of a bead by bead_hash
    GetParents {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Get the children hashes of a bead by bead hash
    GetChildren {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Get the list of beads in the highest work path
    GetHwPath {
        /// Limit the number of results
        limit: u8,
    },

    /// Get statistics about the IPC connection
    GetIpcStats,

    /// Get braid information (similar to getblockchaininfo in bitcoin-cli)
    GetBraidInfo,

    /// Get node information (libp2p PeerID, payout address, miner pubkey, etc.)
    GetNodeInfo {
        /// The node identifier (bead hash)
        node: String,
    },

    /// Get peer information (IP/PeerID/libp2p address of connected peers)
    GetPeerInfo,

    /// Get the list of transactions staged for the next bead we mine
    StagedTransactions,

    /// Get transactions committed in beads but not yet mined
    CommittedTransactions,

    /// Get transactions in the blocktemplate we're currently mining
    BlockStagedTransactions,

    /// Add a transaction to our staged list
    StageTransactions {
        /// Transaction ID (from bitcoind) or full transaction
        tx_id: String,
    },

    /// Remove a transaction from our stage list by txid
    UnstageTransactions {
        /// Transaction ID to remove
        tx_id: String,
    },

    /// Proxy a Bitcoin RPC call to bitcoind
    /// Example: braidpool-cli bitcoin getblockchaininfo
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

#[derive(Deserialize, Debug)]
struct JsonRpcResponse {
    result: serde_json::Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<serde_json::Value>,
}

/// Client-side RPC call function
async fn call_rpc(
    rpc_url: &str,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let rpc_request = JsonRpcRequest {
        jsonrpc: "2.0",
        method: method.to_string(),
        params,
        id: 1,
    };

    let client = reqwest::Client::new();
    let res = client.post(rpc_url).json(&rpc_request).send().await?;

    if res.status().is_success() {
        let rpc_response: JsonRpcResponse = res.json().await?;
        if let Some(error) = rpc_response.error {
            return Err(format!("RPC error: {}", error).into());
        }
        Ok(rpc_response.result)
    } else {
        let status = res.status();
        let text = res
            .text()
            .await
            .unwrap_or_else(|_| "Could not read error body".to_string());
        Err(format!("HTTP error: {}\nResponse: {}", status, text).into())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let (method, params) = match &cli.commands {
        Commands::GetBead { bead_hash } => ("getbead", json!([bead_hash])),
        Commands::AddBead { bead_data } => ("addbead", json!([bead_data])),
        Commands::GetBeadCount => ("getbeadcount", json!([])),
        Commands::GetCohortCount => ("getcohortcount", json!([])),
        Commands::GetTips => ("gettips", json!([])),
        Commands::GetCohort { cohort_id } => ("getcohort", json!([cohort_id])),
        Commands::GetGenesis => ("getgenesis", json!([])),
        Commands::GetMinerInfo => ("getminerinfo", json!([])),
        Commands::GetMiner { connection_id } => ("getminer", json!([connection_id])),
        Commands::GetMiningInfo => ("getmininginfo", json!([])),
        Commands::GetParents { bead_hash } => ("getparents", json!([bead_hash])),
        Commands::GetChildren { bead_hash } => ("getchildren", json!([bead_hash])),
        Commands::GetHwPath { limit } => ("gethwpath", json!([limit])),
        Commands::GetIpcStats => ("getipcstats", json!([])),
        Commands::GetBraidInfo => ("getbraidinfo", json!([])),
        Commands::GetNodeInfo { node } => ("getnodeinfo", json!([node])),
        Commands::GetPeerInfo => ("getpeerinfo", json!([])),
        Commands::StagedTransactions => ("stagedtransactions", json!([])),
        Commands::CommittedTransactions => ("committedtransactions", json!([])),
        Commands::BlockStagedTransactions => ("blockstagedtransactions", json!([])),
        Commands::StageTransactions { tx_id } => ("stagetransactions", json!([tx_id])),
        Commands::UnstageTransactions { tx_id } => ("unstagetransactions", json!([tx_id])),
        Commands::Bitcoin { method, params } => {
            let params_value: serde_json::Value =
                serde_json::from_str(params).unwrap_or_else(|_| json!([]));
            ("bitcoinproxy", json!([method, params_value]))
        }
    };

    match call_rpc(&cli.rpc_url, method, params).await {
        Ok(result) => {
            let pretty_response = serde_json::to_string_pretty(&result)?;
            println!("{}", pretty_response);
            Ok(())
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            std::process::exit(1);
        }
    }
}
