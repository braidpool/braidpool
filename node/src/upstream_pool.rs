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
    pub share_id: crate::audit::ShareId,
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
    /// Tracks pending share submissions: request_id -> (worker_name, original_request_id, sent_at, share_id)
    pending_shares: HashMap<u64, (String, u64, std::time::Instant, crate::audit::ShareId)>,
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
    /// Shared reference to the Braid structure for bead/audit operations
    braid_arc: Arc<tokio::sync::RwLock<crate::braid::Braid>>,
    /// Channel for sending upstream share responses and events with ShareId to the audit log
    audit_log_tx: mpsc::Sender<(crate::audit::ShareId, Value)>,
    // Track subscribe handshake request ID
    subscribe_req_id: Option<u64>,
    // Track authorize handshake requet ID
    authorize_req_id: Option<u64>,
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
        braid_arc: Arc<tokio::sync::RwLock<crate::braid::Braid>>,
        audit_log_tx: mpsc::Sender<(crate::audit::ShareId, Value)>,
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
            braid_arc,
            audit_log_tx,
            subscribe_req_id: None,
            authorize_req_id: None,
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
                .with_time(StdDuration::from_secs(300))
                .with_interval(StdDuration::from_secs(2))
                .with_retries(3);

            let sockref = socket2::SockRef::from(&stream);
            if let Err(e) = sockref.set_tcp_keepalive(&keepalive) {
                error!("Failed to set TCP keepalive: {}", e);
                return Err(StratumErrors::UpstreamConnectionFailed {
                    error: format!("Keepalive config failed: {}", e),
                });
            }
            info!("TCP keepalive enabled: idle=300s, interval=2s, retries=3 (dead connection detected in ~306s)");
        }

        #[cfg(not(target_os = "linux"))]
        {
            use std::time::Duration as StdDuration;
            let keepalive = socket2::TcpKeepalive::new()
                .with_time(StdDuration::from_secs(300))
                .with_interval(StdDuration::from_secs(2));

            let sockref = socket2::SockRef::from(&stream);
            if let Err(e) = sockref.set_tcp_keepalive(&keepalive) {
                warn!("Failed to set TCP keepalive: {}", e);
            } else {
                #[cfg(any(target_os = "macos", target_os = "windows"))]
                info!("TCP keepalive enabled: idle=30s, interval=2s (dead connection detected in ~310-330s, system default retries)");

                #[cfg(not(any(target_os = "macos", target_os = "windows")))]
                info!("TCP keepalive enabled: idle=300s, interval=2s (platform-specific detection time)");
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
        self.subscribe_req_id = None;
        self.authorize_req_id = None;

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
                    self.pending_shares.retain(|request_id, (worker_name, _original_id, sent_at, _share_id)| {
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
        let request_id = self.next_request_id;
        self.subscribe_req_id = Some(request_id);

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
        let request_id = self.next_request_id;
        self.authorize_req_id = Some(request_id);

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
                    if let Some((worker_name, original_request_id, _sent_at, share_id)) =
                        self.pending_shares.remove(&request_id)
                    {
                        info!(
                            "Received share response for {} (upstream_id={}, miner_id={})",
                            worker_name, request_id, original_request_id
                        );
                        let accepted = if let Some(result) = msg.get("result") {
                            if result.is_null() {
                                msg.get("error").map_or(false, |e| e.is_null())
                            } else {
                                result == &json!(true)
                            }
                        } else {
                            false
                        };
                        if accepted {
                            info!("SHARE ACCEPTED by upstream pool for {}", worker_name);
                        } else {
                            error!("SHARE REJECTED by upstream pool for {}", worker_name);
                            if let Some(error) = msg.get("error") {
                                if let Some(error_arr) = error.as_array() {
                                    let error_code =
                                        error_arr.get(0).and_then(|v| v.as_i64()).unwrap_or(-1);
                                    let error_msg = error_arr
                                        .get(1)
                                        .and_then(|v| v.as_str())
                                        .unwrap_or("unknown");
                                    error!("Rejection details [{}]: {}", error_code, error_msg);
                                } else {
                                    error!("Rejection reason: {:?}", error);
                                }
                            }
                        }
                        if let Err(e) = self
                            .audit_log_tx
                            .send((share_id.clone(), msg.clone()))
                            .await
                        {
                            error!("Failed to send to audit log: {}", e);
                        }
                        return Ok(());
                    }

                    // Handle subscribe response
                    if Some(request_id) == self.subscribe_req_id
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

                    // Handle authorize response
                    if Some(request_id) == self.authorize_req_id && msg.get("result").is_some() {
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

                    let bead_hash = {
                        let braid = self.braid_arc.read().await;

                        if let Some(&latest_tip_idx) = braid.tips.iter().next() {
                            if let Some(bead) = braid.beads.get(latest_tip_idx) {
                                crate::audit::compute_audit_bead_hash(bead)
                            } else {
                                bitcoin::BlockHash::from_byte_array([0u8; 32])
                            }
                        } else {
                            bitcoin::BlockHash::from_byte_array([0u8; 32])
                        }
                    };
                    if let Err(e) = self
                        .notification_tx
                        .send(NotifyCmd::UpdateExtranonce {
                            new_bead_hash: bead_hash,
                        })
                        .await
                    {
                        error!(
                            bead_hash = %bead_hash,
                            error = %e,
                            "Failed to send extranonce update command to notifier"
                        );
                    } else {
                        debug!(
                            bead_hash = %bead_hash,
                            "Sent extranonce update command to notifier"
                        );
                    }

                    // cache the job
                    {
                        let mut cache = self.upstream_cache.write().await;
                        cache.set_latest_job(job.clone());
                    }

                    let should_log_stats = self.next_request_id % 10 == 0;
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

        let version_bits_for_log = share.version_bits.clone();
        if let Some(version_bits) = share.version_bits {
            params.push(json!(version_bits));
        }
        debug!(
            worker = %share.worker_name,
            job_id = %share.job_id,
            extranonce2 = %share.extranonce2,
            extranonce2_len = %share.extranonce2.len(),
            ntime = %share.ntime,
            nonce = %share.nonce,
            version_bits = ?version_bits_for_log,
            upstream_username = %self.config.username,
            "Forwarding share to upstream with params"
        );
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
                share.share_id.clone(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::braid::Braid;
    use bitcoin::BlockHash;
    use serde_json::json;
    use std::time::Duration;
    use tokio::sync::mpsc;

    /// Helper to create a test UpstreamPoolClient with disconnected channels for parsing tests
    fn create_test_client() -> (
        UpstreamPoolClient,
        mpsc::Receiver<JobNotification>,
        mpsc::Receiver<NotifyCmd>,
    ) {
        let config = UpstreamPoolConfig {
            hostname: "test.pool".to_string(),
            port: 3333,
            username: "test".to_string(),
            password: "pass".to_string(),
        };

        let (_share_tx, share_rx) = mpsc::channel(10);
        let (job_tx, job_rx) = mpsc::channel(10);
        let (notification_tx, notification_rx) = mpsc::channel(10);
        let (response_tx, _response_rx) = mpsc::channel(10);
        let (_configure_tx, configure_rx) = mpsc::channel(10);
        let (audit_log_tx, _audit_log_rx) = mpsc::channel(10);

        let client = UpstreamPoolClient::new(
            config,
            Arc::new(tokio::sync::Mutex::new(share_rx)),
            job_tx,
            notification_tx,
            response_tx,
            None,
            None,
            Arc::new(tokio::sync::Mutex::new(configure_rx)),
            UpstreamCache::new(),
            Arc::new(tokio::sync::RwLock::new(Braid::new(vec![]))),
            audit_log_tx,
        );

        (client, job_rx, notification_rx)
    }

    #[test]
    /// Verify that a newly instantiated UpstreamCache has all fields safely initialized to None.
    fn test_upstream_cache_default() {
        let cache = UpstreamCache::default();
        assert!(cache.configure_response.is_none());
        assert!(cache.subscribe_response.is_none());
        assert!(cache.current_difficulty.is_none());
        assert!(cache.latest_job.is_none());
    }

    #[test]
    /// Verify that CachedItem correctly tracks its age, resets its timestamp on updates, and properly reports expiration when its TTL elapses.
    fn test_cached_item_lifecycle() {
        let mut item = CachedItem::new("value".to_string(), 60);

        assert!(item.is_valid());
        assert_eq!(item.age_seconds(), 0);

        let time_before = item.cached_at;
        std::thread::sleep(Duration::from_millis(10));
        item.update("new_value".to_string());

        assert_eq!(item.value, "new_value");
        assert!(
            item.cached_at > time_before,
            "Timestamp should be newer after update"
        );

        // Expiry test
        let expired_item = CachedItem::new("expired", 0);
        std::thread::sleep(Duration::from_millis(1));
        assert!(!expired_item.is_valid());
    }

    #[test]
    /// Verify that subscribe responses, including the extranonce details and nested subscription arrays, are accurately cached and retrieved.
    fn test_cache_subscribe_response() {
        let mut cache = UpstreamCache::default();
        let subscriptions = vec![
            ("mining.notify".to_string(), "sub_id_1".to_string()),
            ("mining.set_difficulty".to_string(), "sub_id_2".to_string()),
        ];

        cache.set_subscribe("aabbccdd".to_string(), 8, &subscriptions);

        let cached = cache.get_subscribe().unwrap();
        assert_eq!(cached.extranonce1, "aabbccdd");
        assert_eq!(cached.extranonce2_size, 8);
        assert_eq!(cached.subscriptions.len(), 2);
        assert_eq!(cached.subscriptions[0].0, "mining.notify");
    }

    #[test]
    /// Verify that caching a new job with the 'clean_jobs' flag set to true correctly overrides and replaces the previously cached job.
    fn test_cache_job_clean_jobs() {
        let mut cache = UpstreamCache::default();

        let mut dummy_job = JobNotification {
            job_id: "job1".to_string(),
            prevhash: "000".to_string(),
            coinbase1: "cb1".to_string(),
            coinbase2: "cb2".to_string(),
            merkle_branches: vec![],
            version: "20000000".to_string(),
            nbits: "1d00ffff".to_string(),
            ntime: "507c0000".to_string(),
            clean_jobs: false,
            coinbase_witness_commitment: None,
            parsed_bits: Some(bitcoin::CompactTarget::from_consensus(0x1d00ffff)),
        };

        cache.set_latest_job(dummy_job.clone());
        assert_eq!(cache.get_latest_job().unwrap().job_id, "job1");

        // New job with clean_jobs=true should overwrite immediately
        dummy_job.job_id = "job2".to_string();
        dummy_job.clean_jobs = true;
        cache.set_latest_job(dummy_job);

        assert_eq!(cache.get_latest_job().unwrap().job_id, "job2");
        assert!(cache.get_latest_job().unwrap().clean_jobs);
    }

    #[test]
    /// Verify that cache statistics accurately reflect the internal state and that the clear() method completely wipes all stored session data.
    fn test_cache_clear_and_stats() {
        let mut cache = UpstreamCache::default();

        cache.set_configure(json!({"test": true}));
        cache.set_difficulty(1024.0);

        let stats = cache.stats();
        assert!(stats.configure_valid);
        assert!(stats.difficulty_valid);
        assert_eq!(stats.difficulty_value, Some(1024.0));

        cache.clear();

        let empty_stats = cache.stats();
        assert!(!empty_stats.configure_valid);
        assert!(!empty_stats.difficulty_valid);
        assert!(cache.configure_response.is_none());
        assert!(cache.current_difficulty.is_none());
    }

    #[test]
    /// Verify that a standard, well formed Stratum V1 mining.notify parameter array is parsed perfectly into a valid JobNotification struct.
    fn test_parse_upstream_job_valid() {
        let (client, _, _) = create_test_client();

        let params = vec![
            json!("job_id_123"),
            json!("0000000000000000000000000000000000000000000000000000000000000000"),
            json!("01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff"),
            json!("ffffffff00000000"),
            json!(["hash1", "hash2"]),
            json!("20000000"),
            json!("1d00ffff"),
            json!("507c0000"),
            json!(true),
        ];

        let result = client.parse_upstream_job(&params);
        assert!(result.is_ok(), "Valid job should parse successfully");

        let job = result.unwrap();
        assert_eq!(job.job_id, "job_id_123");
        assert_eq!(job.merkle_branches.len(), 2);
        assert!(job.clean_jobs);
        assert!(job.parsed_bits.is_some());
    }

    #[test]
    /// Verify that the parser correctly throws a ParamNotFound error when mandatory fields like job_id or prevhash are
    /// completely missing or empty.
    fn test_parse_upstream_job_missing_params() {
        let (client, _, _) = create_test_client();

        // Missing job_id
        let mut params = vec![
            json!(""),
            json!("0000000000000000"),
            json!("cb1"),
            json!("cb2"),
            json!([]),
            json!("20000000"),
            json!("1d00ffff"),
            json!("507c0000"),
        ];

        let result = client.parse_upstream_job(&params);
        match result {
            Err(StratumErrors::ParamNotFound { param, .. }) => assert_eq!(param, "job_id"),
            _ => panic!("Expected ParamNotFound error for job_id"),
        }

        // Missing prevhash
        params[0] = json!("job123");
        params[1] = json!("");
        let result2 = client.parse_upstream_job(&params);
        match result2 {
            Err(StratumErrors::ParamNotFound { param, .. }) => assert_eq!(param, "prevhash"),
            _ => panic!("Expected ParamNotFound error for prevhash"),
        }
    }

    #[test]
    /// Verify that the parser correctly rejects a job and throws an InvalidMethodParams error if the nbits field contains
    /// non-hexadecimal characters.
    fn test_parse_upstream_job_invalid_nbits() {
        let (client, _, _) = create_test_client();

        let params = vec![
            json!("job123"),
            json!("0000000"),
            json!("cb1"),
            json!("cb2"),
            json!([]),
            json!("20000000"),
            json!("GGGGGGGG"), // Invalid hex
            json!("507c0000"),
        ];

        match client.parse_upstream_job(&params) {
            Err(StratumErrors::InvalidMethodParams { method }) => {
                assert!(method.contains("not valid hex"));
            }
            _ => panic!("Expected InvalidMethodParams error for bad nbits"),
        }
    }

    #[test]
    /// Verify that the parser explicitly rejects jobs with an nbits value of zero to prevent potential divide-by-zero or
    /// downstream consensus errors.
    fn test_parse_upstream_job_zero_nbits() {
        let (client, _, _) = create_test_client();

        let params = vec![
            json!("job123"),
            json!("0000000"),
            json!("cb1"),
            json!("cb2"),
            json!([]),
            json!("20000000"),
            json!("00000000"),
            json!("507c0000"),
        ];

        match client.parse_upstream_job(&params) {
            Err(StratumErrors::InvalidMethodParams { method }) => {
                assert!(method.contains("nbits cannot be zero"));
            }
            _ => panic!("Expected InvalidMethodParams error for zero nbits"),
        }
    }

    #[test]
    /// Verify that optional parameters, such as the clean_jobs boolean, properly default to safe values when omitted
    /// from the upstream message.
    fn test_parse_upstream_job_defaults() {
        let (client, _, _) = create_test_client();

        let params = vec![
            json!("job123"),
            json!("00000"),
            json!("cb1"),
            json!("cb2"),
            json!([]),
            json!("20"),
            json!("1d00ffff"),
            json!("507c0000"),
        ];

        let job = client.parse_upstream_job(&params).unwrap();
        assert!(!job.clean_jobs, "clean_jobs should default to false");
        assert_eq!(job.merkle_branches.len(), 0);
    }

    #[tokio::test]
    /// Verify that the client intercepts and safely rejects outbound shares if the miner's extranonce2 length does not exactly match
    /// the size required by the upstream pool.
    async fn test_forward_share_invalid_extranonce2_length() {
        let (mut client, _, _) = create_test_client();

        client.extranonce1 = Some("b34cf004".to_string());
        client.extranonce2_size = Some(4);

        let invalid_share = UpstreamShare {
            worker_name: "test_worker".to_string(),
            job_id: "job1".to_string(),
            extranonce2: "001122".to_string(),
            ntime: "ntime".to_string(),
            nonce: "nonce".to_string(),
            version_bits: None,
            original_request_id: 1,
            share_id: BlockHash::from_byte_array([0u8; 32]),
        };

        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let stream = tokio::net::TcpStream::connect(addr).await.unwrap();
        let (_, mut dummy_writer) = stream.into_split();

        // The method should catch the invalid length and return an error before trying to write
        let result = client.forward_share(&mut dummy_writer, invalid_share).await;

        match result {
            Err(StratumErrors::InvalidMethodParams { method }) => {
                assert!(method.contains("wrong length"));
                assert!(method.contains("expected 8 hex chars"));
            }
            _ => panic!("Expected InvalidMethodParams due to wrong extranonce2 length"),
        }
    }
}
