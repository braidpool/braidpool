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
use std::sync::Arc;
use tokio::sync::RwLock;
use tokio::time::Duration;

const WRITE_TIMEOUT: Duration = Duration::from_secs(5);

/// Unified cache for all upstream pool data
#[derive(Debug, Clone)]
pub struct UpstreamCache {
    /// Cached mining.configure response (version rolling mask, etc.)
    pub configure_response: Option<CachedItem<Value>>,

    /// Cached mining.subscribe response (extranonce1, extranonce2_size)
    pub subscribe_response: Option<CachedItem<UpstreamSubscribeResponse>>,

    /// Current difficulty from upstream
    pub current_difficulty: Option<CachedItem<f64>>,

    /// Most recent job notification
    pub latest_job: Option<CachedItem<JobNotification>>,
}

/// Individual cache item with its own timestamp and TTL
#[derive(Debug, Clone)]
pub struct CachedItem<T> {
    /// The cached value
    pub value: T,

    /// When this item was cached
    pub cached_at: std::time::SystemTime,

    /// TTL in seconds, how long this item stays valid
    pub ttl_seconds: u64,
}

impl<T: Clone> CachedItem<T> {
    /// Create a new cached item with default TTL
    pub fn new(value: T, ttl_seconds: u64) -> Self {
        Self {
            value,
            cached_at: std::time::SystemTime::now(),
            ttl_seconds,
        }
    }

    /// Check if this cached item is still valid
    pub fn is_valid(&self) -> bool {
        match self.cached_at.elapsed() {
            Ok(duration) => duration.as_secs() < self.ttl_seconds,
            Err(_) => false,
        }
    }

    /// Get age in seconds
    pub fn age_seconds(&self) -> u64 {
        self.cached_at.elapsed().map(|d| d.as_secs()).unwrap_or(0)
    }

    /// Update value and reset timestamp
    pub fn update(&mut self, new_value: T) {
        self.value = new_value;
        self.cached_at = std::time::SystemTime::now();
    }
}

#[derive(Debug, Clone)]
pub struct UpstreamSubscribeResponse {
    pub extranonce1: String,
    pub extranonce2_size: usize,
    pub subscriptions: Vec<(String, String)>,
}

impl Default for UpstreamCache {
    fn default() -> Self {
        Self {
            configure_response: None,
            subscribe_response: None,
            current_difficulty: None,
            latest_job: None,
        }
    }
}

impl UpstreamCache {
    pub fn new() -> Arc<RwLock<Self>> {
        Arc::new(RwLock::new(Self::default()))
    }

    pub fn clear(&mut self) {
        info!("Clearing upstream cache due to new connection");
        self.configure_response = None;
        self.subscribe_response = None;
        self.current_difficulty = None;
        self.latest_job = None;
    }

    /// Cache mining.configure response
    pub fn set_configure(&mut self, response: Value) {
        self.configure_response = Some(CachedItem::new(response, u64::MAX));
        info!("Cached upstream mining.configure response");
    }

    /// Get cached configure response if valid
    pub fn get_configure(&self) -> Option<&Value> {
        self.configure_response
            .as_ref()
            .filter(|item| item.is_valid())
            .map(|item| &item.value)
    }

    pub fn set_subscribe(
        &mut self,
        extranonce1: String,
        extranonce2_size: usize,
        subscriptions: &[(String, String)],
    ) {
        self.subscribe_response = Some(CachedItem::new(
            UpstreamSubscribeResponse {
                extranonce1,
                extranonce2_size,
                subscriptions: subscriptions.to_vec(),
            },
            u64::MAX,
        ));
        info!(
            "Cached upstream mining.subscribe response with {} subscriptions",
            self.subscribe_response
                .as_ref()
                .unwrap()
                .value
                .subscriptions
                .len()
        );
    }

    /// Get cached subscribe response if valid
    pub fn get_subscribe(&self) -> Option<&UpstreamSubscribeResponse> {
        self.subscribe_response
            .as_ref()
            .filter(|item| item.is_valid())
            .map(|item| &item.value)
    }

    /// Cache difficulty
    pub fn set_difficulty(&mut self, difficulty: f64) {
        self.current_difficulty = Some(CachedItem::new(difficulty, u64::MAX));
        info!("Cached upstream difficulty: {}", difficulty);
    }

    /// Get cached difficulty if valid
    pub fn get_difficulty(&self) -> Option<f64> {
        self.current_difficulty
            .as_ref()
            .filter(|item| item.is_valid())
            .map(|item| item.value)
    }

    /// Cache latest job notification, 1 hour TTL, but respects clean_jobs
    pub fn set_latest_job(&mut self, job: JobNotification) {
        // If clean_jobs=true, invalidate old job first
        if job.clean_jobs {
            info!("Job has clean_jobs=true, invalidating old cache");
            self.latest_job = None;
        }

        self.latest_job = Some(CachedItem::new(job.clone(), 3600)); // 1 hour

        info!(
            job_id = %job.job_id,
            clean_jobs = %job.clean_jobs,
            "Cached upstream job"
        );
    }

    /// Get cached job if valid
    pub fn get_latest_job(&self) -> Option<&JobNotification> {
        self.latest_job
            .as_ref()
            .filter(|item| item.is_valid())
            .map(|item| &item.value)
    }

    /// Force invalidate job cache (e.g., on upstream disconnect)
    pub fn invalidate_job(&mut self) {
        info!("Manually invalidating job cache");
        self.latest_job = None;
    }

    /// cache statistics
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            configure_cached: self.configure_response.is_some(),
            configure_valid: self.get_configure().is_some(),

            subscribe_cached: self.subscribe_response.is_some(),
            subscribe_valid: self.get_subscribe().is_some(),

            difficulty_cached: self.current_difficulty.is_some(),
            difficulty_valid: self.get_difficulty().is_some(),
            difficulty_value: self.get_difficulty(),

            job_cached: self.latest_job.is_some(),
            job_valid: self.get_latest_job().is_some(),
            job_id: self.get_latest_job().map(|j| j.job_id.clone()),
            job_age_seconds: self.latest_job.as_ref().map(|item| item.age_seconds()),
        }
    }

    /// Log current cache state, mainly useful for debugging
    pub fn log_stats(&self) {
        let stats = self.stats();
        info!(
            "Cache stats [Cached/Valid]: configure={}/{}, subscribe={}/{}, difficulty={}/{}, job={}/{} (age={}s, id={:?})",
            stats.configure_cached, stats.configure_valid,
            stats.subscribe_cached, stats.subscribe_valid,
            stats.difficulty_cached, stats.difficulty_valid,
            stats.job_cached, stats.job_valid,
            stats.job_age_seconds.unwrap_or(0),
            stats.job_id
        );
    }
}

#[derive(Debug, Clone)]
pub struct CacheStats {
    pub configure_cached: bool,
    pub configure_valid: bool,

    pub subscribe_cached: bool,
    pub subscribe_valid: bool,

    pub difficulty_cached: bool,
    pub difficulty_valid: bool,
    pub difficulty_value: Option<f64>,

    pub job_cached: bool,
    pub job_valid: bool,
    pub job_id: Option<String>,
    pub job_age_seconds: Option<u64>,
}

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
    /// Upstream pool connection configuration (hostname, port, credentials)
    config: UpstreamPoolConfig,
    /// Receive shares from miners to forward upstream
    share_rx: Arc<tokio::sync::Mutex<mpsc::Receiver<UpstreamShare>>>,
    /// Send jobs from upstream to notifier
    job_tx: mpsc::Sender<JobNotification>,
    /// Sends protocol notifications to local handlers
    notification_tx: mpsc::Sender<NotifyCmd>,
    /// Send share responses back (worker_name, response, original_request_id)
    response_tx: mpsc::Sender<(String, Value, u64)>,
    /// Cached extranonce1 value received from upstream
    extranonce1: Option<String>,
    /// Cached extranonce2 size received from upstream
    extranonce2_size: Option<usize>,
    /// Current difficulty as set by upstream
    upstream_difficulty: Option<f64>,
    /// Next request ID to use for upstream requests
    next_request_id: u64,
    /// Tracks pending share submissions: request_id -> (worker_name, original_request_id, sent_at)
    pending_shares: HashMap<u64, (String, u64, std::time::Instant)>,
    /// Tracks pending configure requests: request_id -> response channel
    pending_requests: HashMap<u64, mpsc::Sender<Value>>,
    /// Sends updated extranonce values to the stratum server
    extranonce_tx: Option<mpsc::Sender<(String, usize)>>,
    /// Sends updated difficulty values to the stratum server
    difficulty_tx: Option<mpsc::Sender<f64>>,
    /// Receives mining.configure requests from miners to be forwarded upstream
    configure_rx: Arc<tokio::sync::Mutex<mpsc::Receiver<(Value, u64, mpsc::Sender<Value>)>>>,
    /// Shared cache for upstream responses and state
    upstream_cache: Arc<RwLock<UpstreamCache>>,
}

impl UpstreamPoolClient {
    pub fn new(
        config: UpstreamPoolConfig,
        share_rx: Arc<tokio::sync::Mutex<mpsc::Receiver<UpstreamShare>>>,
        job_tx: mpsc::Sender<JobNotification>,
        notification_tx: mpsc::Sender<NotifyCmd>,
        response_tx: mpsc::Sender<(String, Value, u64)>,
        extranonce_tx: Option<mpsc::Sender<(String, usize)>>,
        difficulty_tx: Option<mpsc::Sender<f64>>,
        configure_rx: Arc<tokio::sync::Mutex<mpsc::Receiver<(Value, u64, mpsc::Sender<Value>)>>>,
        upstream_cache: Arc<RwLock<UpstreamCache>>,
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
            upstream_cache,
        }
    }

    /// Connect to upstream pool and handle bidirectional communication
    pub async fn run(mut self) -> Result<(), StratumErrors> {
        info!(
            "Connecting to upstream pool at {}:{}",
            self.config.hostname, self.config.port
        );

        self.connect_and_run().await
    }

    /// Single connection attempt, handles all communication until disconnect
    async fn connect_and_run(&mut self) -> Result<(), StratumErrors> {
        let addr = format!("{}:{}", self.config.hostname, self.config.port);

        // Connection with timeout
        let stream =
            match tokio::time::timeout(Duration::from_secs(30), TcpStream::connect(&addr)).await {
                Ok(Ok(stream)) => stream,
                Ok(Err(e)) => {
                    return Err(StratumErrors::UpstreamConnectionFailed {
                        error: format!("Connection failed: {}", e),
                    });
                }
                Err(_) => {
                    return Err(StratumErrors::UpstreamConnectionFailed {
                        error: "Connection timeout".to_string(),
                    });
                }
            };

        // Set TCP keepalive
        if let Err(e) = stream.set_nodelay(true) {
            warn!("Failed to set TCP_NODELAY: {}", e);
        }

        #[cfg(target_os = "linux")]
        {
            use std::time::Duration as StdDuration;
            let keepalive = socket2::TcpKeepalive::new()
                .with_time(StdDuration::from_secs(30))
                .with_interval(StdDuration::from_secs(2))
                .with_retries(3);

            let sockref = socket2::SockRef::from(&stream);
            if let Err(e) = sockref.set_tcp_keepalive(&keepalive) {
                error!("Failed to set TCP keepalive: {}", e);
                return Err(StratumErrors::UpstreamConnectionFailed {
                    error: format!("Keepalive config failed: {}", e),
                });
            }
            info!("TCP keepalive enabled: idle=30s, interval=2s, retries=3 (dead connection detected in ~36s)");
        }

        #[cfg(not(target_os = "linux"))]
        {
            use std::time::Duration as StdDuration;
            let keepalive = socket2::TcpKeepalive::new()
                .with_time(StdDuration::from_secs(30))
                .with_interval(StdDuration::from_secs(2));

            let sockref = socket2::SockRef::from(&stream);
            if let Err(e) = sockref.set_tcp_keepalive(&keepalive) {
                warn!("Failed to set TCP keepalive: {}", e);
            } else {
                #[cfg(any(target_os = "macos", target_os = "windows"))]
                info!("TCP keepalive enabled: idle=30s, interval=2s (dead connection detected in ~60-90s, system default retries)");

                #[cfg(not(any(target_os = "macos", target_os = "windows")))]
                info!("TCP keepalive enabled: idle=30s, interval=2s (platform-specific detection time)");
            }
        }

        let (reader, mut writer) = stream.into_split();
        let reader = BufReader::new(reader);
        let mut framed = FramedRead::new(reader, LinesCodec::new_with_max_length(64 * 1024));
        // Reset state for new connection
        self.extranonce1 = None;
        self.extranonce2_size = None;
        self.pending_shares.clear();
        self.pending_requests.clear();
        self.next_request_id = 1;
        self.upstream_cache.write().await.clear();

        // Send initial handshake
        self.send_subscribe(&mut writer).await?;
        self.send_authorize(&mut writer).await?;
        info!("Connected to upstream pool at {}", addr);

        let mut cleanup_interval = tokio::time::interval(Duration::from_secs(30));
        let mut last_activity = std::time::Instant::now();
        let activity_timeout = Duration::from_secs(120);
        let read_timeout = Duration::from_secs(30);

        // Main event loop
        loop {
            tokio::select! {
                // Handle incoming messages from upstream
               result = tokio::time::timeout(read_timeout, framed.next()) => {
                    match result {
                        Ok(Some(Ok(line))) => {
                            last_activity = std::time::Instant::now();
                            if let Err(e) = self.handle_upstream_message(&line).await {
                                error!("Error handling upstream message: {:?}", e);
                            }
                        }
                        Ok(Some(Err(e))) => {
                            error!("Error reading from upstream: {}", e);
                            return Err(StratumErrors::UpstreamConnectionFailed {
                                error: format!("Read error: {}", e),
                            });
                        }
                        Ok(None) => {
                            warn!("Upstream connection closed by server");
                            return Err(StratumErrors::UpstreamConnectionFailed {
                                error: "Connection closed by upstream".to_string(),
                            });
                        }
                        Err(_elapsed) => {
                            // Read timeout, check if connection is dead
                            let elapsed_since_activity = last_activity.elapsed();
                            if elapsed_since_activity > activity_timeout {
                                error!(
                                    "No upstream activity for {:?} - connection dead",
                                    elapsed_since_activity
                                );
                                return Err(StratumErrors::UpstreamConnectionFailed {
                                    error: format!(
                                        "No activity for {:?}",
                                        elapsed_since_activity
                                    ),
                                });
                            } else {
                                debug!(
                                    "Read timeout after {:?}, last activity {:?} ago - continuing",
                                    read_timeout,
                                    elapsed_since_activity
                                );
                                // Continue the loop, not a dead connection yet
                                continue;
                            }
                        }
                    }
                }

                // Forward shares from miners to upstream
                share = async {
                    let mut rx = self.share_rx.lock().await;
                    rx.recv().await
                } => {
                    match share {
                        Some(share) => {
                            // Check queue depth after every Nth (100) share
                            let check_frequency = 100;
                            if self.next_request_id % check_frequency == 0 {
                                let pending_count = {
                                    let rx = self.share_rx.lock().await;
                                    rx.len()
                                };

                                if pending_count > 5000 {
                                    error!(
                                        "Upstream share queue critically high: {} shares pending",
                                        pending_count
                                    );
                                    error!("Upstream pool may be slow or disconnected");
                                } else if pending_count > 1000 {
                                    warn!(
                                        "Upstream share queue growing: {} shares pending",
                                        pending_count
                                    );
                                } else if pending_count > 0 && pending_count % 100 == 0 {
                                    debug!("Upstream share queue: {} shares pending", pending_count);
                                }
                            }

                            if self.extranonce1.is_none() {
                                warn!(
                                    "Cannot forward share for {} - upstream extranonce not set yet",
                                    share.worker_name
                                );
                                // Send error response back to miner
                                if let Err(e) = self.response_tx.send((
                                    share.worker_name.clone(),
                                    serde_json::json!({
                                        "id": share.original_request_id,
                                        "result": null,
                                        "error": [21, "Upstream not ready", null]
                                    }),
                                    share.original_request_id
                                )).await {
                                    error!("Failed to send error response: {}", e);
                                }
                                continue;
                            }

                            match tokio::time::timeout(
                                WRITE_TIMEOUT,
                                self.forward_share(&mut writer, share.clone())
                            ).await {
                                Ok(Ok(())) => {
                                    // Share forwarded successfully
                                    last_activity = std::time::Instant::now();
                                }
                                Ok(Err(e)) => {
                                    error!("Failed to forward share: {:?}", e);
                                    // Connection might be broken, return to trigger reconnect
                                    return Err(e);
                                }
                                Err(_elapsed) => {
                                    error!(
                                        "Share write timed out after {:?} for worker {}",
                                        WRITE_TIMEOUT,
                                        share.worker_name
                                    );
                                    // Send error back to miner
                                    let _ = self.response_tx.send((
                                        share.worker_name.clone(),
                                        serde_json::json!({
                                            "id": share.original_request_id,
                                            "result": null,
                                            "error": [23, "Share write timeout", null]
                                        }),
                                        share.original_request_id
                                    )).await;

                                    // Connection is likely dead, trigger reconnect
                                    return Err(StratumErrors::UpstreamConnectionFailed {
                                        error: format!(
                                            "Share write timeout after {:?}",
                                            WRITE_TIMEOUT
                                        ),
                                    });
                                }
                            }
                        }
                        None => {
                            // All share senders dropped, very unlikely
                            warn!("Share channel closed unexpectedly");
                        }
                    }
                }

                // Handle mining.configure requests from miners
                configure = async {
                    let mut rx = self.configure_rx.lock().await;
                    rx.recv().await
                } => {
                    match configure {
                        Some((params, request_id, response_tx)) => {
                            // Check cache first
                            let cache = self.upstream_cache.read().await;

                            if let Some(cached_response) = &cache.configure_response {
                                if cached_response.is_valid() {
                                    info!("Serving mining.configure from cache");

                                    let response = serde_json::json!({
                                        "id": request_id,
                                        "result": cached_response.value.get("result").cloned().unwrap_or(serde_json::json!({})),
                                        "error": null
                                    });

                                    if let Err(e) = response_tx.send(response).await {
                                        error!("Failed to send cached configure response: {}", e);
                                    }

                                    drop(cache);
                                    continue;
                                }
                            }

                            drop(cache);

                            // If cache miss or expired, forward to upstream
                            info!("Cache miss for mining.configure - forwarding to upstream pool");

                           match tokio::time::timeout(
                                WRITE_TIMEOUT,
                                self.forward_configure(&mut writer, &params, request_id, response_tx.clone())
                            ).await {
                                Ok(Ok(())) => {
                                    // Configure forwarded successfully
                                    last_activity = std::time::Instant::now();
                                    info!("Configure forwarded successfully");
                                }
                                Ok(Err(e)) => {
                                    error!("Failed to forward configure: {:?}", e);
                                    // Send error back to miner
                                    let _ = response_tx.send(serde_json::json!({
                                        "id": request_id,
                                        "result": null,
                                        "error": [24, "Configure forward failed", null]
                                    })).await;

                                    return Err(StratumErrors::UpstreamConnectionFailed {
                                        error: "Configure forward failed".to_string(),
                                    });
                                }
                                Err(_elapsed) => {
                                    error!(
                                        "Configure write timed out after {:?}",
                                        WRITE_TIMEOUT
                                    );
                                    // Send error back to miner
                                    let _ = response_tx.send(serde_json::json!({
                                        "id": request_id,
                                        "result": null,
                                        "error": [23, "Configure write timeout", null]
                                    })).await;

                                    // kill connection for configure timeouts
                                    return Err(StratumErrors::UpstreamConnectionFailed {
                                        error: format!("Configure write timeout after {:?}", WRITE_TIMEOUT),
                                    });
                                }
                            }
                        }
                        None => {
                            warn!("Configure channel closed unexpectedly");
                        }
                    }
                }

                // Periodic cleanup of stale requests
                _ = cleanup_interval.tick() => {
                    if last_activity.elapsed() > activity_timeout {
                        error!(
                            "No upstream activity in {:?}, assuming dead connection",
                            activity_timeout
                        );
                        return Err(StratumErrors::UpstreamConnectionFailed {
                            error: "Connection timeout - no activity".to_string(),
                        });
                    }

                    // Clean up stale pending requests
                    let before = self.pending_requests.len();
                    self.pending_requests.retain(|_, tx| !tx.is_closed());
                    let cleaned = before - self.pending_requests.len();
                    if cleaned > 0 {
                        debug!(
                            cleaned_requests = cleaned,
                            remaining = self.pending_requests.len(),
                            "Cleaned up stale configure requests"
                        );
                    }

                    // Clean up stale pending shares (older than 60 seconds)
                    let now = std::time::Instant::now();
                    let timeout = Duration::from_secs(60);
                    let before_shares = self.pending_shares.len();
                    self.pending_shares.retain(|request_id, (worker_name, _original_id, sent_at)| {
                        let age = now.duration_since(*sent_at);
                        if age > timeout {
                            warn!(
                                "Share from {} (request_id={}) timed out after {:?} - upstream never responded",
                                worker_name,
                                request_id,
                                age
                            );
                            false  // Remove this entry
                        } else {
                            true  // Keep this entry
                        }
                    });
                    let cleaned_shares = before_shares - self.pending_shares.len();
                    if cleaned_shares > 0 {
                        warn!(
                            cleaned_shares = cleaned_shares,
                            remaining = self.pending_shares.len(),
                            "Cleaned up {} stale pending shares that upstream never responded to",
                            cleaned_shares
                        );
                    }
                    if self.pending_shares.len() > 100 || self.pending_requests.len() > 10 {
                        warn!(
                            "High pending counts - shares: {}, requests: {}",
                            self.pending_shares.len(),
                            self.pending_requests.len()
                        );
                    }

                    {
                        let mut cache = self.upstream_cache.write().await;

                        if let Some(ref job_item) = cache.latest_job {
                            if !job_item.is_valid() {
                                warn!(
                                    "Removing expired job from cache (age={}s, job_id={:?})",
                                    job_item.age_seconds(),
                                    job_item.value.job_id
                                );
                                cache.latest_job = None;
                            }
                        }
                    }

                    // Log cache stats periodically
                    let cache = self.upstream_cache.read().await;
                    cache.log_stats();
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
        tokio::time::timeout(WRITE_TIMEOUT, async {
            writer.write_all(msg.as_bytes()).await?;
            writer.flush().await
        })
        .await
        .map_err(|_| StratumErrors::UpstreamConnectionFailed {
            error: format!("Subscribe write timeout after {:?}", WRITE_TIMEOUT),
        })?
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
        tokio::time::timeout(WRITE_TIMEOUT, async {
            writer.write_all(msg.as_bytes()).await?;
            writer.flush().await
        })
        .await
        .map_err(|_| StratumErrors::UpstreamConnectionFailed {
            error: format!("Authorize write timeout after {:?}", WRITE_TIMEOUT),
        })?
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

        // Check if this is a response (has "id" field that's not null)
        if let Some(id) = msg.get("id") {
            // Skip if id is null (notifications don't have numeric IDs)
            if !id.is_null() {
                if let Some(request_id) = id.as_u64() {
                    // Check if this is a pending configure request
                    if let Some(response_tx) = self.pending_requests.remove(&request_id) {
                        info!("Received configure response from upstream, caching it");
                        let msg_clone = msg.clone();

                        // Cache the response for future use
                        {
                            let mut cache = self.upstream_cache.write().await;
                            cache.set_configure(msg_clone);
                        }

                        if let Err(e) = response_tx.send(msg.clone()).await {
                            error!("Failed to forward response to miner: {}", e);
                        }
                        return Ok(()); // return early, don't process further
                    }

                    // Check if this is a pending share response
                    if let Some((worker_name, original_request_id, _sent_at)) =
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
                                // Parse subscriptions array
                                let subscriptions: Vec<(String, String)> = result
                                    .get(0)
                                    .and_then(|v| v.as_array())
                                    .map(|subs| {
                                        subs.iter()
                                            .filter_map(|sub| {
                                                if let Some(arr) = sub.as_array() {
                                                    if arr.len() >= 2 {
                                                        let method = arr[0].as_str()?.to_string();
                                                        let id = arr[1].as_str()?.to_string();
                                                        return Some((method, id));
                                                    }
                                                }
                                                None
                                            })
                                            .collect()
                                    })
                                    .unwrap_or_default();

                                info!("Upstream subscriptions: {:?}", subscriptions);

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
                                // Cache subscribe response
                                if let (Some(extranonce1), Some(extranonce2_size)) =
                                    (&self.extranonce1, self.extranonce2_size)
                                {
                                    let ext1_clone = extranonce1.clone();
                                    {
                                        let mut cache = self.upstream_cache.write().await;
                                        cache.set_subscribe(
                                            ext1_clone,
                                            extranonce2_size,
                                            &subscriptions,
                                        );
                                    }
                                    info!(
                                        "Cached upstream subscribe response with {} subscriptions",
                                        subscriptions.len()
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
                    let should_log_stats = self.next_request_id % 10 == 0;

                    // cache the job
                    {
                        let mut cache = self.upstream_cache.write().await;
                        cache.set_latest_job(job.clone());
                    }

                    // Log cache stats every 10 jobs
                    if should_log_stats {
                        let cache = self.upstream_cache.read().await;
                        cache.log_stats();
                    }

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

                        // Cache difficulty
                        {
                            let mut cache = self.upstream_cache.write().await;
                            cache.set_difficulty(difficulty);
                        }

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

                        // cache extranonce
                        if let (Some(ref extranonce1), Some(extranonce2_size)) =
                            (&self.extranonce1, self.extranonce2_size)
                        {
                            let ext1_clone = extranonce1.clone();
                            let existing_subs = {
                                let cache = self.upstream_cache.read().await;
                                cache
                                    .get_subscribe()
                                    .map(|sub_resp| sub_resp.subscriptions.clone())
                                    .unwrap_or_default()
                            };
                            {
                                let mut cache = self.upstream_cache.write().await;
                                cache.set_subscribe(ext1_clone, extranonce2_size, &existing_subs);
                            }
                            info!("Updated cached extranonce from mining.set_extranonce (preserved {} subscriptions)", 
                                existing_subs.len());
                        }

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
            (
                share.worker_name.clone(),
                share.original_request_id,
                std::time::Instant::now(),
            ),
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

        debug!(
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
        self.pending_requests.retain(|_, tx| !tx.is_closed());
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
