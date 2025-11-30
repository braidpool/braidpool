// src/upstream_pool.rs
use serde_json::{json, Value};
use std::collections::HashMap;
use tokio::{
    io::{AsyncWriteExt, BufReader},
    net::TcpStream,
    sync::mpsc,
};
use tokio_stream::StreamExt;
use tokio_util::codec::{FramedRead, LinesCodec};
use tracing::{debug, error, info, warn};

use crate::error::StratumErrors;
use crate::stratum::{JobNotification, NotifyCmd};

/// Configuration for upstream pool connection
#[derive(Debug, Clone)]
pub struct UpstreamPoolConfig {
    pub hostname: String,
    pub port: u16,
    pub username: String,
    pub password: String,
}

/// Share to be forwarded to upstream pool
#[derive(Debug, Clone)]
pub struct UpstreamShare {
    pub worker_name: String,
    pub job_id: String,
    pub extranonce2: String,
    pub ntime: String,
    pub nonce: String,
    pub version_bits: Option<String>,
    pub original_request_id: u64,
}

/// Upstream pool client that acts as a miner to the upstream pool
pub struct UpstreamPoolClient {
    config: UpstreamPoolConfig,
    /// Receive shares from miners to forward upstream
    share_rx: mpsc::Receiver<UpstreamShare>,
    /// Send jobs from upstream to notifier
    job_tx: mpsc::Sender<JobNotification>,
    notification_tx: mpsc::Sender<NotifyCmd>,
    /// Send share responses back
    response_tx: mpsc::Sender<(String, Value, u64)>, //  (worker_name, response, original_request_id)

    /// Upstream connection state
    extranonce1: Option<String>,
    extranonce2_size: Option<usize>,
    upstream_difficulty: Option<f64>,
    next_request_id: u64,

    pending_shares: HashMap<u64, (String, u64)>,
    pending_requests: HashMap<u64, mpsc::Sender<Value>>,

    extranonce_tx: Option<mpsc::Sender<(String, usize)>>,

    difficulty_tx: Option<mpsc::Sender<f64>>,

    configure_rx: mpsc::Receiver<(Value, u64, mpsc::Sender<Value>)>,
}

impl UpstreamPoolClient {
    pub fn new(
        config: UpstreamPoolConfig,
        share_rx: mpsc::Receiver<UpstreamShare>,
        job_tx: mpsc::Sender<JobNotification>,
        notification_tx: mpsc::Sender<NotifyCmd>,
        response_tx: mpsc::Sender<(String, Value, u64)>,
        extranonce_tx: Option<mpsc::Sender<(String, usize)>>,
        difficulty_tx: Option<mpsc::Sender<f64>>,
        configure_rx: mpsc::Receiver<(Value, u64, mpsc::Sender<Value>)>,
    ) -> Self {
        Self {
            config,
            share_rx,
            job_tx,
            notification_tx,
            response_tx,
            extranonce1: None,
            extranonce2_size: None,
            upstream_difficulty: None,
            next_request_id: 1,
            pending_shares: HashMap::new(),
            pending_requests: HashMap::new(),
            extranonce_tx,
            difficulty_tx,
            configure_rx,
        }
    }

    /// Connect to upstream pool and handle bidirectional communication
    pub async fn run(mut self) -> Result<(), StratumErrors> {
        let mut retry_delay = std::time::Duration::from_secs(5);
        let max_retry_delay = std::time::Duration::from_secs(60);

        loop {
            info!(
                "Connecting to upstream pool at {}:{}",
                self.config.hostname, self.config.port
            );

            match self.connect_and_run().await {
                Ok(_) => {
                    info!("Upstream pool client disconnected gracefully");
                    // Graceful disconnect, don't reconnect
                    return Ok(());
                }
                Err(e) => {
                    error!("Upstream connection error: {:?}", e);
                    info!("Reconnecting in {:?}...", retry_delay);
                    tokio::time::sleep(retry_delay).await;
                    // Exponential backoff with max cap
                    retry_delay = std::cmp::min(retry_delay * 2, max_retry_delay);
                }
            }
        }
    }

    /// Single connection attempt, handles all communication until disconnect
    async fn connect_and_run(&mut self) -> Result<(), StratumErrors> {
        let addr = format!("{}:{}", self.config.hostname, self.config.port);
        let stream = TcpStream::connect(&addr).await.map_err(|e| {
            StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            }
        })?;

        let (reader, mut writer) = stream.into_split();
        let reader = BufReader::new(reader);
        let mut framed = FramedRead::new(reader, LinesCodec::new());

        // Reset state for new connection
        self.extranonce1 = None;
        self.extranonce2_size = None;
        self.pending_shares.clear();
        self.pending_requests.clear();
        self.next_request_id = 1;
        self.send_subscribe(&mut writer).await?;
        self.send_authorize(&mut writer).await?;
        info!("Connected to upstream pool");

        // Main event loop
        loop {
            tokio::select! {
                // Handle incoming messages from upstream
                result = framed.next() => {
                    match result {
                        Some(Ok(line)) => {
                            self.handle_upstream_message(&line).await?;
                        }
                        Some(Err(e)) => {
                            error!("Error reading from upstream: {}", e);
                            return Err(StratumErrors::UpstreamConnectionFailed {
                                error: e.to_string(),
                            });
                        }
                        None => {
                            warn!("Upstream connection closed");
                            return Err(StratumErrors::UpstreamConnectionFailed {
                                error: "Connection closed by upstream".to_string(),
                            });
                        }
                    }
                }
                // Forward shares from miners to upstream
                Some(share) = self.share_rx.recv() => {
                    if let Err(e) = self.forward_share(&mut writer, share).await {
                        error!("Failed to forward share: {:?}", e);
                    }
                }
                // Handle mining.configure requests from miners
                Some((params, request_id, response_tx)) = self.configure_rx.recv() => {
                    if let Err(e) = self.forward_configure(&mut writer, &params, request_id, response_tx).await {
                        error!("Failed to forward configure: {:?}", e);
                    }
                }
                else => {
                    warn!("All channels closed, exiting upstream pool client");
                    return Ok(()); // Graceful exit
                }
            }
        }
    }

    async fn send_subscribe(
        &mut self,
        writer: &mut tokio::net::tcp::OwnedWriteHalf,
    ) -> Result<(), StratumErrors> {
        let subscribe_req = json!({
            "id": self.next_request_id,
            "method": "mining.subscribe",
            "params": ["Braidpool/1.0.0"]
        });
        self.next_request_id += 1;
        let msg = format!("{}\n", subscribe_req);
        writer.write_all(msg.as_bytes()).await.map_err(|e| {
            StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            }
        })?;
        writer
            .flush()
            .await
            .map_err(|e| StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            })?;

        info!("Sent subscribe to upstream pool");
        Ok(())
    }

    async fn send_authorize(
        &mut self,
        writer: &mut tokio::net::tcp::OwnedWriteHalf,
    ) -> Result<(), StratumErrors> {
        let authorize_req = json!({
            "id": self.next_request_id,
            "method": "mining.authorize",
            "params": [self.config.username, self.config.password]
        });
        self.next_request_id += 1;
        let msg = format!("{}\n", authorize_req);
        writer.write_all(msg.as_bytes()).await.map_err(|e| {
            StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            }
        })?;
        writer
            .flush()
            .await
            .map_err(|e| StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            })?;
        info!("Sent authorize to upstream pool");
        Ok(())
    }

    async fn handle_upstream_message(&mut self, line: &str) -> Result<(), StratumErrors> {
        debug!("Raw upstream message: {}", line);

        let msg: Value = serde_json::from_str(line).map_err(|e| {
            error!("Failed to parse upstream message: {}", e);
            StratumErrors::InvalidMethodParams {
                method: "upstream_parse".to_string(),
            }
        })?;

        debug!(
            "Pending requests: {:?}",
            self.pending_requests.keys().collect::<Vec<_>>()
        );
        debug!(
            "Pending shares: {:?}",
            self.pending_shares.keys().collect::<Vec<_>>()
        );

        // Check if this is a response (has "id" field that's not null)
        if let Some(id) = msg.get("id") {
            // Skip if id is null (notifications don't have numeric IDs)
            if !id.is_null() {
                if let Some(request_id) = id.as_u64() {
                    // Check if this is a pending configure request
                    if let Some(response_tx) = self.pending_requests.remove(&request_id) {
                        info!("Received response for pending request {}", request_id);
                        if let Err(e) = response_tx.send(msg.clone()).await {
                            error!("Failed to forward response to miner: {}", e);
                        }
                        return Ok(()); // return early, don't process further
                    }

                    // Check if this is a pending share response
                    if let Some((worker_name, original_request_id)) =
                        self.pending_shares.remove(&request_id)
                    {
                        info!(
                            "Received share response for {} (upstream_id={}, miner_id={})",
                            worker_name, request_id, original_request_id
                        );

                        // Check if share was accepted or rejected
                        if let Some(result) = msg.get("result") {
                            if result.is_null() {
                                // Result is null, check error field
                                if let Some(error) = msg.get("error") {
                                    if error.is_null() {
                                        // Both result and error are null, but treat as success
                                        warn!(
                                            "Share response has null result and null error for {}",
                                            worker_name
                                        );
                                    } else {
                                        // Error is not null, share rejected
                                        error!(
                                            "SHARE REJECTED by upstream pool for worker: {}",
                                            worker_name
                                        );
                                        error!("Error code: {:?}", error);
                                        // Parse error details
                                        if let Some(error_arr) = error.as_array() {
                                            let error_code = error_arr
                                                .get(0)
                                                .and_then(|v| v.as_i64())
                                                .unwrap_or(-1);
                                            let error_msg = error_arr
                                                .get(1)
                                                .and_then(|v| v.as_str())
                                                .unwrap_or("unknown");
                                            error!("Error [{}]: {}", error_code, error_msg);
                                        } else {
                                            error!("Error details: {:?}", error);
                                        }
                                    }
                                } else {
                                    // Result is null but no error field
                                    warn!(
                                        "Share response for {} has null result and no error field",
                                        worker_name
                                    );
                                }
                            } else {
                                // Result is not null, check if true
                                if result == &json!(true) {
                                    info!(
                                        "SHARE ACCEPTED!!! by upstream pool for worker: {}",
                                        worker_name
                                    );
                                    info!("Share successfully submitted to Ocean!");
                                } else {
                                    warn!(
                                        "Share response for {} has unexpected result: {:?}",
                                        worker_name, result
                                    );
                                }
                            }
                        } else {
                            // No result field at all
                            error!("Share response for {} missing 'result' field", worker_name);
                        }

                        // Forward the response back to main.rs
                        if let Err(e) = self
                            .response_tx
                            .send((worker_name.clone(), msg.clone(), original_request_id))
                            .await
                        {
                            error!("Failed to forward share response to main: {}", e);
                        }
                        return Ok(());
                    }

                    // Handle subscribe response
                    if request_id == 1
                        && msg.get("result").is_some()
                        && msg.get("error").map_or(true, |e| e.is_null())
                    {
                        // Subscribe response, parse extranonce
                        if let Some(result) = msg.get("result").and_then(|r| r.as_array()) {
                            // result = [[subscriptions], extranonce1, extranonce2_size]
                            if result.len() >= 3 {
                                // Handle nested array for subscriptions, extranonce1 might be at index 1
                                // Check if result[0] is an array (subscriptions) or string (some pools format differently)
                                let (ext1_idx, ext2_idx) =
                                    if result.get(0).map_or(false, |v| v.is_array()) {
                                        (1, 2) // Standard format: [[subs], extranonce1, extranonce2_size]
                                    } else {
                                        (1, 2) // Same indices, just verify
                                    };

                                self.extranonce1 = result
                                    .get(ext1_idx)
                                    .and_then(|v| v.as_str())
                                    .map(String::from);
                                self.extranonce2_size = result
                                    .get(ext2_idx)
                                    .and_then(|v| v.as_u64())
                                    .map(|v| v as usize);

                                info!("Upstream subscribe successful!");
                                info!("Extranonce1: {:?}", self.extranonce1);
                                info!("Extranonce2 size: {:?}", self.extranonce2_size);

                                if let Some(ext2_size) = self.extranonce2_size {
                                    info!(
                                        "Upstream extranonce2 size: {} bytes = {} hex characters",
                                        ext2_size,
                                        ext2_size * 2
                                    );
                                }

                                // Send extranonce to stratum server
                                if let Some(ref tx) = self.extranonce_tx {
                                    if let (Some(ref ext1), Some(ext2_size)) =
                                        (&self.extranonce1, self.extranonce2_size)
                                    {
                                        if let Err(e) = tx.send((ext1.clone(), ext2_size)).await {
                                            error!("Failed to send extranonce to stratum: {}", e);
                                        } else {
                                            info!("Sent upstream extranonce to stratum server");
                                        }
                                    }
                                }
                            }
                        }
                        return Ok(());
                    }

                    // Handle authorize response (id=2 typically)
                    if request_id == 2 && msg.get("result").is_some() {
                        if let Some(result) = msg.get("result") {
                            if result == &json!(true) {
                                info!("Upstream authorize successful!");
                            } else {
                                error!("Upstream authorize failed: {:?}", msg.get("error"));
                            }
                        }
                        return Ok(());
                    }

                    // Unknown response with numeric id
                    warn!(
                        "Received response for unknown request_id={}: {:?}",
                        request_id, msg
                    );
                }
            }
        }

        // Handle notifications (no id, or id is null) - mining.notify, mining.set_difficulty
        if let Some(method) = msg.get("method").and_then(|m| m.as_str()) {
            match method {
                "mining.notify" => {
                    let params =
                        msg["params"]
                            .as_array()
                            .ok_or(StratumErrors::InvalidMethodParams {
                                method: "mining.notify".to_string(),
                            })?;

                    // Parse job notification from upstream
                    let job = self.parse_upstream_job(params)?;
                    info!(
                        "Received upstream job: {} (clean={})",
                        job.job_id, job.clean_jobs
                    );
                    debug!("Upstream parsed job: {:?}", job);
                    // Also send to job_tx for main.rs
                    if let Err(e) = self.job_tx.send(job).await {
                        error!("Failed to send job to main: {}", e);
                    }
                }

                "mining.set_difficulty" => {
                    let params =
                        msg["params"]
                            .as_array()
                            .ok_or(StratumErrors::InvalidMethodParams {
                                method: "mining.set_difficulty".to_string(),
                            })?;

                    if let Some(diff_value) = params.get(0) {
                        // Parse difficulty (can be float or integer)
                        let difficulty = if let Some(d) = diff_value.as_f64() {
                            d
                        } else if let Some(d) = diff_value.as_u64() {
                            d as f64
                        } else {
                            error!("Invalid difficulty type from upstream: {:?}", diff_value);
                            return Ok(());
                        };

                        self.upstream_difficulty = Some(difficulty);
                        info!("Upstream difficulty changed to: {}", difficulty);

                        // Broadcast to all miners via notification_tx
                        if let Err(e) = self
                            .notification_tx
                            .send(NotifyCmd::BroadcastDifficulty { difficulty })
                            .await
                        {
                            error!("Failed to send difficulty broadcast: {}", e);
                        }

                        // Also update ConnectionMapping for new subscribers
                        if let Some(ref tx) = self.difficulty_tx {
                            if let Err(e) = tx.send(difficulty).await {
                                error!("Failed to update ConnectionMapping with difficulty: {}", e);
                            }
                        }
                    }
                }

                "mining.set_extranonce" => {
                    // Some pools send this to update extranonce mid-session
                    let params =
                        msg["params"]
                            .as_array()
                            .ok_or(StratumErrors::InvalidMethodParams {
                                method: "mining.set_extranonce".to_string(),
                            })?;

                    if params.len() >= 2 {
                        self.extranonce1 = params.get(0).and_then(|v| v.as_str()).map(String::from);
                        self.extranonce2_size =
                            params.get(1).and_then(|v| v.as_u64()).map(|v| v as usize);

                        info!(
                            "Upstream extranonce updated: {:?}, size={:?}",
                            self.extranonce1, self.extranonce2_size
                        );

                        // Send updated extranonce to stratum server
                        if let Some(ref tx) = self.extranonce_tx {
                            if let (Some(ref ext1), Some(ext2_size)) =
                                (&self.extranonce1, self.extranonce2_size)
                            {
                                if let Err(e) = tx.send((ext1.clone(), ext2_size)).await {
                                    error!("Failed to send updated extranonce to stratum: {}", e);
                                }
                            }
                        }
                    }
                }

                _ => {
                    debug!("Unhandled upstream method: {}", method);
                }
            }
        }

        Ok(())
    }

    fn parse_upstream_job(&self, params: &[Value]) -> Result<JobNotification, StratumErrors> {
        let job_id = params
            .get(0)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job missing or empty job_id");
                StratumErrors::ParamNotFound {
                    param: "job_id".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        let prevhash = params
            .get(1)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job {} missing or empty prevhash", job_id);
                StratumErrors::ParamNotFound {
                    param: "prevhash".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        let coinbase1 = params
            .get(2)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job {} missing or empty coinbase1", job_id);
                StratumErrors::ParamNotFound {
                    param: "coinbase1".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        let coinbase2 = params
            .get(3)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job {} missing or empty coinbase2", job_id);
                StratumErrors::ParamNotFound {
                    param: "coinbase2".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        let merkle_branches: Vec<String> = params
            .get(4)
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default();

        let version = params
            .get(5)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job {} missing or empty version", job_id);
                StratumErrors::ParamNotFound {
                    param: "version".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        let nbits_str = params
            .get(6)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job {} missing or empty nbits", job_id);
                StratumErrors::ParamNotFound {
                    param: "nbits".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        let parsed_bits = match u32::from_str_radix(&nbits_str, 16) {
            Ok(bits_u32) => {
                if bits_u32 == 0 {
                    error!("Upstream job {} has zero nbits", job_id);
                    return Err(StratumErrors::InvalidMethodParams {
                        method: "mining.notify: nbits cannot be zero".to_string(),
                    });
                }
                Some(bitcoin::CompactTarget::from_consensus(bits_u32))
            }
            Err(e) => {
                error!(
                    "Upstream job {} has invalid nbits '{}': {}",
                    job_id, nbits_str, e
                );
                return Err(StratumErrors::InvalidMethodParams {
                    method: format!(
                        "mining.notify: nbits '{}' is not valid hex: {}",
                        nbits_str, e
                    ),
                });
            }
        };

        let ntime = params
            .get(7)
            .and_then(|v| v.as_str())
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                error!("Upstream job {} missing or empty ntime", job_id);
                StratumErrors::ParamNotFound {
                    param: "ntime".to_string(),
                    method: "mining.notify".to_string(),
                }
            })?
            .to_string();

        // clean_jobs is optional, defaults to false
        let clean_jobs = params.get(8).and_then(|v| v.as_bool()).unwrap_or(false);

        // Parse upstream mining.notify params
        Ok(JobNotification {
            job_id,
            prevhash,
            coinbase1,
            coinbase2,
            merkle_branches,
            version,
            nbits: nbits_str,
            ntime,
            clean_jobs,
            coinbase_witness_commitment: None,
            parsed_bits,
        })
    }

    async fn forward_share(
        &mut self,
        writer: &mut tokio::net::tcp::OwnedWriteHalf,
        share: UpstreamShare,
    ) -> Result<(), StratumErrors> {
        if self.extranonce1.is_none() {
            error!(
                "Cannot forward share for {}, upstream extranonce1 not set!",
                share.worker_name
            );
            return Err(StratumErrors::UpstreamShareForwardFailed {
                error: "Upstream extranonce1 not configured, share cannot be forwarded".to_string(),
            });
        }

        if let Some(expected_size) = self.extranonce2_size {
            let expected_hex_len = expected_size * 2; // where each byte = 2 hex chars
            let actual_hex_len = share.extranonce2.len();

            if actual_hex_len != expected_hex_len {
                error!(
                    "Invalid extranonce2 length for worker {}: expected {} hex chars ({} bytes), got {} hex chars",
                    share.worker_name,
                    expected_hex_len,
                    expected_size,
                    actual_hex_len
                );
                return Err(StratumErrors::InvalidMethodParams {
                    method: format!(
                        "mining.submit: extranonce2 '{}' has wrong length (expected {} hex chars)",
                        share.extranonce2, expected_hex_len
                    ),
                });
            }

            // validate it's valid hex
            if hex::decode(&share.extranonce2).is_err() {
                error!(
                    "Invalid extranonce2 hex for worker {}: '{}'",
                    share.worker_name, share.extranonce2
                );
                return Err(StratumErrors::InvalidMethodParams {
                    method: format!(
                        "mining.submit: extranonce2 '{}' is not valid hex",
                        share.extranonce2
                    ),
                });
            }
        } else {
            warn!("Cannot validate extranonce2 length, upstream extranonce2_size not set");
        }

        let mut params = vec![
            json!(self.config.username),
            json!(share.job_id),
            json!(share.extranonce2),
            json!(share.ntime),
            json!(share.nonce),
        ];

        if let Some(version_bits) = share.version_bits {
            params.push(json!(version_bits));
        }

        let request_id = self.next_request_id;
        let submit_req = json!({
            "id": request_id,
            "method": "mining.submit",
            "params": params
        });
        self.next_request_id += 1;

        // Track request_id -> worker_name mapping
        self.pending_shares.insert(
            request_id,
            (share.worker_name.clone(), share.original_request_id),
        );
        let msg = format!("{}\n", submit_req);
        writer.write_all(msg.as_bytes()).await.map_err(|e| {
            StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            }
        })?;

        writer
            .flush()
            .await
            .map_err(|e| StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            })?;

        info!(
            "Forwarded share from {} to upstream (request_id={})",
            share.worker_name, request_id
        );
        Ok(())
    }

    pub async fn forward_configure(
        &mut self,
        writer: &mut tokio::net::tcp::OwnedWriteHalf,
        params: &Value,
        _request_id: u64,
        response_tx: mpsc::Sender<Value>,
    ) -> Result<(), StratumErrors> {
        let configure_req = json!({
            "id": self.next_request_id,
            "method": "mining.configure",
            "params": params
        });

        let upstream_request_id = self.next_request_id;
        self.next_request_id += 1;

        // Store response channel for this request
        self.pending_requests
            .insert(upstream_request_id, response_tx);

        let msg = format!("{}\n", configure_req);
        writer.write_all(msg.as_bytes()).await.map_err(|e| {
            StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            }
        })?;

        writer
            .flush()
            .await
            .map_err(|e| StratumErrors::UpstreamConnectionFailed {
                error: e.to_string(),
            })?;

        info!("Forwarded mining.configure to upstream pool");
        Ok(())
    }
}
