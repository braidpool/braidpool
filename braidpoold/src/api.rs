use axum::{
    extract::Path,
    http::StatusCode,
    routing::{get, post},
    Json, Router,
};
use bitcoincore_rpc::bitcoin::Amount;
use bitcoincore_rpc::bitcoin::{Transaction, Txid};
use bitcoincore_rpc::{Auth, Client, RpcApi};
use futures::stream::{self, StreamExt};
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Serialize)]
struct ApiStatus {
    confirmed: bool,
    block_height: Option<u64>,
    block_hash: Option<String>,
    block_time: Option<u64>,
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
pub struct ApiTransaction {
    pub txid: String,
    pub hash: String,
    pub category: String, // Mempool | Committed | Proposed | Scheduled | Confirmed
    pub size: u64,
    pub weight: Option<u64>,
    pub fee: f64,
    pub fee_rate: f64,
    pub inputs: usize,
    pub outputs: usize,
    pub confirmations: u32,
    pub timestamp: Option<u64>,
    pub rbf_signaled: bool,
    pub status: ApiStatus,
}

#[derive(Serialize)]
pub struct ApiMempoolInfo {
    pub count: usize,
    pub vsize: u64,
    pub total_fee: u64,
    pub fee_histogram: Vec<[f64; 2]>,
}
pub(crate) struct StateStore {
    committed: HashSet<Txid>, // Stage 2: In cmempool
    proposed: HashSet<Txid>,  // Stage 3: Marked as proposed
    scheduled: HashSet<Txid>, // Stage 4: Marked as scheduled
}

impl StateStore {
    fn new() -> Self {
        StateStore {
            committed: HashSet::new(),
            proposed: HashSet::new(),
            scheduled: HashSet::new(),
        }
    }
}

static STATE: Lazy<Mutex<StateStore>> = Lazy::new(|| Mutex::new(StateStore::new()));
static SEEN: Lazy<Mutex<HashMap<Txid, u64>>> = Lazy::new(|| Mutex::new(HashMap::new()));

fn connect_to_bitcoind() -> Client {
    Client::new(
        "http://127.0.0.1:18332",
        Auth::UserPass("jevinrpc".to_string(), "securepass123".to_string()),
    )
    .expect("Failed to connect to bitcoind_node")
}

fn connect_to_cmempoold() -> Client {
    Client::new(
        "http://127.0.0.1:19443",
        Auth::UserPass("cmempoolrpc".to_string(), "securepass456".to_string()),
    )
    .expect("Failed to connect to cmempoold_node")
}

fn now_ts() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

fn to_sats(amount: Amount) -> u64 {
    amount.to_sat()
}

fn to_btc_from_sats(sats: u64) -> f64 {
    (sats as f64) / 100_000_000.0
}

fn detect_category(txid: &Txid, in_std: bool, in_cpool: bool, confirmations: u32) -> String {
    // Priority: Confirmed > Scheduled > Proposed > Committed > Mempool

    if confirmations > 0 {
        return "Confirmed".to_string();
    }

    let state = STATE.lock().unwrap();

    // Stage 4: Scheduled (highest priority for unconfirmed)
    if state.scheduled.contains(txid) {
        return "Scheduled".to_string();
    }

    // Stage 3: Proposed
    if state.proposed.contains(txid) {
        return "Proposed".to_string();
    }

    // Stage 2: Committed (in cmempool_node)
    if in_cpool || state.committed.contains(txid) {
        return "Committed".to_string();
    }

    // Stage 1: Mempool (in bitcoind_node only)
    if in_std {
        return "Mempool".to_string();
    }

    // Replaced
    let mut seen = SEEN.lock().unwrap();
    if seen.remove(txid).is_some() {
        return "Replaced".to_string();
    }

    "Unknown".to_string()
}

fn record_seen(txid: &Txid, in_any_mempool: bool, ts: u64) {
    if in_any_mempool {
        SEEN.lock().unwrap().insert(*txid, ts);
    }
}

fn build_tx(txid: Txid, standard: &Client, committed: &Client) -> ApiTransaction {
    let in_std_entry = standard.get_mempool_entry(&txid).ok();
    let in_cpool_entry = committed.get_mempool_entry(&txid).ok();

    let raw_info = standard
        .get_raw_transaction_info(&txid, None)
        .or_else(|_| committed.get_raw_transaction_info(&txid, None))
        .ok();

    let (confirmations, block_hash, block_time, vsize_raw, inputs, outputs) =
        if let Some(info) = &raw_info {
            (
                info.confirmations.unwrap_or(0) as u32,
                info.blockhash.map(|h| h.to_string()),
                info.blocktime.map(|t| t as u64),
                info.vsize as u64,
                info.vin.len(),
                info.vout.len(),
            )
        } else {
            (0, None, None, 0, 0, 0)
        };

    let mempool = in_std_entry.as_ref().or(in_cpool_entry.as_ref());
    let (vsize, fee_sats, ts_mempool_time, rbf_signaled) = if let Some(e) = mempool {
        (
            e.vsize as u64,
            to_sats(e.fees.base),
            Some(e.time as u64),
            e.bip125_replaceable,
        )
    } else {
        (vsize_raw, 0, None, false)
    };

    let fee_rate = if vsize > 0 {
        (fee_sats as f64) / (vsize as f64)
    } else {
        0.0
    };

    let in_std = in_std_entry.is_some();
    let in_cpool = in_cpool_entry.is_some();
    let category = detect_category(&txid, in_std, in_cpool, confirmations);

    let ts = ts_mempool_time.or(block_time).unwrap_or_else(now_ts);
    record_seen(&txid, in_std || in_cpool, ts);

    // Cleanup if confirmed
    if confirmations > 0 {
        let mut state = STATE.lock().unwrap();
        state.committed.remove(&txid);
        state.proposed.remove(&txid);
        state.scheduled.remove(&txid);
    }

    ApiTransaction {
        txid: txid.to_string(),
        hash: txid.to_string(),
        category,
        size: vsize,
        weight: None,
        fee: to_btc_from_sats(fee_sats),
        fee_rate,
        inputs,
        outputs,
        confirmations,
        timestamp: ts_mempool_time.or(block_time),
        rbf_signaled,
        status: ApiStatus {
            confirmed: confirmations > 0,
            block_height: None,
            block_hash,
            block_time,
        },
    }
}

pub async fn get_transactions() -> Json<Vec<ApiTransaction>> {
    let standard = Arc::new(connect_to_bitcoind());
    let committed = Arc::new(connect_to_cmempoold());

    let std_txids = standard.get_raw_mempool().unwrap_or_default();
    let cpool_txids = committed.get_raw_mempool().unwrap_or_default();
    let set: BTreeSet<_> = std_txids
        .into_iter()
        .chain(cpool_txids.into_iter())
        .collect();

    let results = stream::iter(set.into_iter())
        .map(|txid| {
            let standard = Arc::clone(&standard);
            let committed = Arc::clone(&committed);
            async move { build_tx(txid, standard.as_ref(), committed.as_ref()) }
        })
        .buffer_unordered(16)
        .collect::<Vec<_>>()
        .await;

    Json(results)
}

// Stage 1 -> 2: Mempool → Committed
pub async fn commit_transaction(Path(txid): Path<String>) -> (StatusCode, Json<serde_json::Value>) {
    let standard = connect_to_bitcoind();
    let committed = connect_to_cmempoold();

    let txid = match txid.parse::<Txid>() {
        Ok(t) => t,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"status":"error","error":format!("invalid txid: {e}")})),
            )
        }
    };

    // Check if already in cmempool
    if committed.get_mempool_entry(&txid).is_ok() {
        STATE.lock().unwrap().committed.insert(txid);
        return (
            StatusCode::OK,
            Json(json!({
                "status":"ok",
                "txid":txid.to_string(),
                "message":"Transaction already committed"
            })),
        );
    }

    // Get transaction from bitcoind
    let tx: Transaction = match standard.get_raw_transaction(&txid, None) {
        Ok(t) => t,
        Err(e) => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"status":"error","error":format!("Transaction not found: {e}")})),
            )
        }
    };

    let std_height = standard.get_block_count().unwrap_or(0);
    let cm_height = committed.get_block_count().unwrap_or(0);

    // Send to cmempool
    match committed.send_raw_transaction(&tx) {
        Ok(_) => {
            STATE.lock().unwrap().committed.insert(txid);
            (
                StatusCode::OK,
                Json(json!({
                    "status":"ok",
                    "txid":txid.to_string(),
                    "message":"Transaction committed to cmempool"
                })),
            )
        }
        Err(e) => {
            let error_str = e.to_string();
            let mut diagnostics = json!({
                "error": error_str.clone(),
                "bitcoind_height": std_height,
                "cmempool_height": cm_height,
            });

            if error_str.contains("-25") || error_str.contains("missing inputs") {
                diagnostics["hint"] = json!("Nodes not synchronized");
            }

            (
                StatusCode::BAD_REQUEST,
                Json(json!({"status":"error","diagnostics":diagnostics})),
            )
        }
    }
}

// Stage 2 -> 3: Committed → Proposed
pub async fn propose_transaction(
    Path(txid): Path<String>,
) -> (StatusCode, Json<serde_json::Value>) {
    let committed = connect_to_cmempoold();

    let txid = match txid.parse::<Txid>() {
        Ok(t) => t,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"status":"error","error":format!("invalid txid: {e}")})),
            )
        }
    };

    // Must be committed first
    let state = STATE.lock().unwrap();
    if !state.committed.contains(&txid) {
        // Check if in cmempool
        if committed.get_mempool_entry(&txid).is_err() {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({
                    "status":"error",
                    "error":"Transaction must be committed first"
                })),
            );
        }
    }
    drop(state);

    STATE.lock().unwrap().proposed.insert(txid);

    (
        StatusCode::OK,
        Json(json!({
            "status":"ok",
            "txid":txid.to_string(),
            "message":"Transaction proposed"
        })),
    )
}

// Stage 3 -> 4: Proposed → Scheduled
pub async fn schedule_transaction(
    Path(txid): Path<String>,
) -> (StatusCode, Json<serde_json::Value>) {
    let txid = match txid.parse::<Txid>() {
        Ok(t) => t,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"status":"error","error":format!("invalid txid: {e}")})),
            )
        }
    };

    // Must be proposed first
    if !STATE.lock().unwrap().proposed.contains(&txid) {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({
                "status":"error",
                "error":"Transaction must be proposed first"
            })),
        );
    }

    STATE.lock().unwrap().scheduled.insert(txid);

    (
        StatusCode::OK,
        Json(json!({
            "status":"ok",
            "txid":txid.to_string(),
            "message":"Transaction scheduled"
        })),
    )
}

// previous endpoint for commit (for backward compatibility)

pub async fn commit_tx_to_cmempoold(
    Path(txid): Path<String>,
) -> (StatusCode, Json<serde_json::Value>) {
    commit_transaction(Path(txid)).await
}

pub async fn get_transaction_detail(Path(txid): Path<String>) -> Json<ApiTransaction> {
    let standard = connect_to_bitcoind();
    let committed = connect_to_cmempoold();
    let txid_parsed = txid.parse::<Txid>().unwrap();
    Json(build_tx(txid_parsed, &standard, &committed))
}

pub async fn get_mempool_info() -> Json<ApiMempoolInfo> {
    let standard = connect_to_bitcoind();
    let committed = connect_to_cmempoold();

    let std_txids = standard.get_raw_mempool().unwrap_or_default();
    let cpool_txids = committed.get_raw_mempool().unwrap_or_default();
    let set: BTreeSet<_> = std_txids
        .into_iter()
        .chain(cpool_txids.into_iter())
        .collect();

    let mut total_vsize: u64 = 0;
    let mut total_fee_sats: u64 = 0;
    let mut histogram: BTreeMap<u64, u64> = BTreeMap::new();

    for txid in set.iter() {
        let entry = standard
            .get_mempool_entry(txid)
            .ok()
            .or_else(|| committed.get_mempool_entry(txid).ok());

        if let Some(e) = entry {
            let vsize = e.vsize as u64;
            let fee_sats = to_sats(e.fees.base);
            total_vsize += vsize;
            total_fee_sats += fee_sats;

            if vsize > 0 {
                let fee_rate = (fee_sats as f64) / (vsize as f64);
                let bucket = fee_rate.round() as u64;
                *histogram.entry(bucket).or_insert(0) += vsize;
            }
        }
    }

    let fee_histogram: Vec<[f64; 2]> = histogram
        .into_iter()
        .map(|(bucket, vsz)| [bucket as f64, vsz as f64])
        .collect();

    Json(ApiMempoolInfo {
        count: set.len(),
        vsize: total_vsize,
        total_fee: total_fee_sats,
        fee_histogram,
    })
}

pub fn build_router() -> Router {
    Router::new()
        .route("/transactions", get(get_transactions))
        .route("/tx/{txid}", get(get_transaction_detail))
        .route("/mempool/info", get(get_mempool_info))
        .route("/beads/commit/{txid}", post(commit_tx_to_cmempoold)) // backward compatibility
        .route("/transactions/{txid}/commit", post(commit_transaction))
        .route("/transactions/{txid}/propose", post(propose_transaction))
        .route("/transactions/{txid}/schedule", post(schedule_transaction))
}
