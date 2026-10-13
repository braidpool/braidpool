use bitcoin::{
    absolute::Height, block::Version as BlockVersion, blockdata::Weight, BlockHash, CompactTarget,
    Target, Transaction, Witness,
};
use bitcoin::hashes::Hash as _;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use crate::TemplateId;

#[derive(Debug, Clone)]
pub struct BlockSubmissionRequest {
    /// The template ID that this submission is for
    pub template_id: TemplateId,
    /// Fully constructed block header (includes version, prevhash, merkle root, time, bits, nonce)
    pub header: bitcoin::block::Header,
    /// Complete coinbase transaction
    pub coinbase_transaction: bitcoin::Transaction,
}

/// Represents the `getblocktemplate` RPC response from Bitcoin Core.
///
/// Based on [BIP-0022](https://github.com/bitcoin/bips/blob/master/bip-0022.mediawiki) and
/// [Bitcoin Core implementation](https://github.com/bitcoin/bitcoin/blob/master/src/rpc/mining.cpp).
///
/// Contains all fields necessary for constructing a valid mining job, including
/// block version, previous block hash, transactions, coinbase data, target, and
/// various consensus limits.
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct BlockTemplate {
    pub version: BlockVersion,
    pub rules: Option<Vec<String>>,
    pub vbavailable: Option<Vec<(String, i32)>>,
    pub vbrequired: Option<u32>,
    pub previousblockhash: BlockHash,
    pub transactions: Vec<Transaction>,
    pub coinbaseaux: Option<Vec<(String, String)>>,
    pub coinbasevalue: Option<u64>,
    pub longpollid: Option<String>,
    pub target: Target,
    pub mintime: Option<u32>,
    pub mutable: Option<Vec<String>>,
    pub noncerange: Option<String>,
    pub sigoplimit: Option<u32>,
    pub sizelimit: Option<usize>,
    pub weightlimit: Option<Weight>,
    pub curtime: u32,
    pub bits: CompactTarget,
    pub height: Height,
    pub default_witness_commitment: Option<Witness>,
}

impl Default for BlockTemplate {
    fn default() -> Self {
        Self {
            version: BlockVersion::TWO,
            rules: None,
            vbavailable: None,
            vbrequired: None,
            previousblockhash: BlockHash::all_zeros(),
            transactions: Vec::new(),
            coinbaseaux: None,
            coinbasevalue: None,
            longpollid: None,
            target: Target::MAX,
            mintime: None,
            mutable: None,
            noncerange: None,
            sigoplimit: None,
            sizelimit: None,
            weightlimit: None,
            curtime: 1759998900,
            bits: CompactTarget::from_consensus(0),
            height: Height::ZERO,
            default_witness_commitment: None,
        }
    }
}

/// Configuration parameters for the Stratum server.
///
/// Defines network binding details, difficulty settings,
/// and optional solo mining payout address.
#[derive(Debug, Clone)]
pub struct StratumServerConfig {
    /// Hostname or IP address to bind the Stratum server.
    pub hostname: String,
    /// Initial mining difficulty assigned to new clients as per in the `braidpool_spec.md`.
    pub start_difficulty: u64,
    /// Minimum allowed mining difficulty as per in the `braidpool_spec.md`.
    pub minimum_difficulty: u64,
    /// Optional maximum allowed mining difficulty.
    pub maximum_difficulty: Option<u64>,
    /// Optional payout address for solo mining mode.
    pub solo_address: Option<String>,
    /// Indicates audit mode.
    pub audit_mode: bool,
    /// Audit mode miner weak difficulty
    pub audit_miner_difficulty: Option<f64>,
}

impl Default for StratumServerConfig {
    fn default() -> Self {
        Self {
            hostname: String::from("0.0.0.0"),
            start_difficulty: 1,
            minimum_difficulty: 1,
            maximum_difficulty: None,
            solo_address: None,
            audit_mode: false,
            audit_miner_difficulty: None,
        }
    }
}

/// Represents a standard `Client → Server` Stratum request.
///
/// Covers common methods such as:
/// - `mining.authorize`
/// - `mining.configure`
/// - `mining.set_difficulty`
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct StandardRequest {
    pub id: u64,
    pub method: String,
    pub params: serde_json::Value,
}

/// Possible responses from the Stratum server.
///
/// Encapsulates both standard JSON-RPC responses and
/// protocol-specific responses such as difficulty suggestions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StratumResponses {
    StandardResponse {
        std_response: StandardResponse,
    },
    SuggestDifficultyResponse {
        suggest_difficulty_resp: SuggestDifficultyResponse,
    },
    PendingUpstreamResponse,
}

/// Response represents a Stratum response message from the server to the client.
/// We use Value in result to allow for different types of responses.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StandardResponse {
    pub id: Option<u64>,
    pub result: Option<Value>,
    pub error: Option<String>,
}

impl StandardResponse {
    pub fn new_ok(id: Option<u64>, result: Value) -> Self {
        StandardResponse {
            id,
            result: Some(result),
            error: None,
        }
    }
}

/// `Notification` method responses specific to `mining.notify` and `mining.set_difficulty`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JobNotificationResponse {
    pub method: String,
    pub params: serde_json::Value,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestDifficultyResponse {
    pub method: String,
    pub params: Vec<u64>,
}

/// Represents a `mining.notify` job message in the Stratum protocol.
///
/// This struct contains all the parameters sent by the mining pool to a miner
/// when a new mining job is assigned. Miners use these values to construct
/// a candidate block header and start hashing.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct JobNotification {
    pub job_id: String,
    pub prevhash: String,
    pub coinbase1: String,
    pub coinbase2: String,
    pub merkle_branches: Vec<String>,
    pub version: String,
    pub nbits: String,
    pub ntime: String,
    pub clean_jobs: bool,
    pub coinbase_witness_commitment: Option<Witness>,
    pub parsed_bits: Option<CompactTarget>,
}

/// `JobDetails` required for tracking jobs available to each downstream node,
/// needed during `mining.submit` validation.
#[derive(Debug, Clone)]
pub struct JobDetails {
    pub blocktemplate: BlockTemplate,
    pub coinbase1: String,
    pub coinbase2: String,
    pub coinbase_merkle_path: Vec<String>,
    pub coinbase_witness_commitment: Option<Witness>,
    pub job_sent_time: u32,
    pub is_upstream_job: bool,
}
