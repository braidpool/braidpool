use std::collections::VecDeque;
use std::error::Error;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use capnp_rpc::{pry, rpc_twoparty_capnp, twoparty, RpcSystem};
use futures::FutureExt;
use tokio::net::UnixStream;
use tokio::sync::{mpsc, oneshot};
use tokio::task::{self, JoinHandle};
use tokio_util::compat::{TokioAsyncReadCompatExt, TokioAsyncWriteCompatExt};

use crate::chain_capnp::{
    chain::Client as ChainClient,
    chain_notifications::{
        BlockConnectedParams, BlockConnectedResults, ChainStateFlushedParams,
        ChainStateFlushedResults, DestroyParams, DestroyResults, UpdatedBlockTipParams,
        UpdatedBlockTipResults,
    },
};

use crate::error::BraidpoolError;
use crate::init_capnp::init::Client as InitClient;
use crate::proxy_capnp::thread::Client as ThreadClient;

pub fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>()
}

// Bitcoin notification events
#[derive(Debug, Clone)]
pub enum BitcoinNotification {
    BlockConnected { height: u32, hash: Vec<u8> },
    UpdatedBlockTip,
    ChainStateFlushed,
    ConnectionLost { reason: String },
}

// Request types with priority
#[derive(Debug)]
enum BitcoinRequest {
    RemoveTransaction {
        txid: Vec<u8>,
        response: oneshot::Sender<Result<bool, String>>,
        priority: RequestPriority,
    },
    RemoveMultipleTransactions {
        txids: Vec<Vec<u8>>,
        response: oneshot::Sender<Result<Vec<(Vec<u8>, bool)>, String>>,
        priority: RequestPriority,
    },
    GetBlockTemplate {
        rules: Option<Vec<String>>,
        response: oneshot::Sender<Result<Vec<u8>, String>>,
        priority: RequestPriority,
    },
    IsInitialBlockDownload {
        response: oneshot::Sender<Result<bool, String>>,
        priority: RequestPriority,
    },
    IsRecentlySynced {
        response: oneshot::Sender<Result<bool, String>>,
        priority: RequestPriority,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RequestPriority {
    Critical = 0,
    High = 1,
    Normal = 2,
    #[allow(dead_code)]
    Low = 3,
}

// Queue metrics
#[derive(Debug, Default)]
pub struct QueueMetrics {
    total_requests: AtomicUsize,
    processed_requests: AtomicUsize,
    failed_requests: AtomicUsize,
    queue_size_critical: AtomicUsize,
    queue_size_high: AtomicUsize,
    queue_size_normal: AtomicUsize,
    queue_size_low: AtomicUsize,
    avg_processing_time_ms: AtomicUsize,
}

#[derive(Debug, Clone)]
pub struct QueueLimits {
    pub critical: usize,
    pub high: usize,
    pub normal: usize,
    pub low: usize,
}

impl Default for QueueLimits {
    fn default() -> Self {
        Self {
            critical: 200,
            high: 500,
            normal: 1000,
            low: 1000,
        }
    }
}

// Priority queue manager
pub struct PriorityRequestQueue {
    critical_queue: VecDeque<BitcoinRequest>,
    high_queue: VecDeque<BitcoinRequest>,
    normal_queue: VecDeque<BitcoinRequest>,
    low_queue: VecDeque<BitcoinRequest>,
    metrics: Arc<QueueMetrics>,
    max_queue_sizes: QueueLimits,
}

impl PriorityRequestQueue {
    fn new(limits: QueueLimits, metrics: Arc<QueueMetrics>) -> Self {
        Self {
            critical_queue: VecDeque::new(),
            high_queue: VecDeque::new(),
            normal_queue: VecDeque::new(),
            low_queue: VecDeque::new(),
            metrics,
            max_queue_sizes: limits,
        }
    }

    fn enqueue(&mut self, request: BitcoinRequest) -> Result<(), BraidpoolError> {
        let priority = match &request {
            BitcoinRequest::IsRecentlySynced { priority, .. } => *priority,
            BitcoinRequest::RemoveTransaction { priority, .. } => *priority,
            BitcoinRequest::RemoveMultipleTransactions { priority, .. } => *priority,
            BitcoinRequest::GetBlockTemplate { priority, .. } => *priority,
            BitcoinRequest::IsInitialBlockDownload { priority, .. } => *priority,
        };

        let result = match priority {
            RequestPriority::Critical => {
                if self.critical_queue.len() >= self.max_queue_sizes.critical {
                    Err(BraidpoolError::QueueFull {
                        queue_type: "Critical".to_string(),
                    })
                } else {
                    self.critical_queue.push_back(request);
                    self.metrics
                        .queue_size_critical
                        .store(self.critical_queue.len(), Ordering::Relaxed);
                    Ok(())
                }
            }
            RequestPriority::High => {
                if self.high_queue.len() >= self.max_queue_sizes.high {
                    Err(BraidpoolError::QueueFull {
                        queue_type: "High".to_string(),
                    })
                } else {
                    self.high_queue.push_back(request);
                    self.metrics
                        .queue_size_high
                        .store(self.high_queue.len(), Ordering::Relaxed);
                    Ok(())
                }
            }
            RequestPriority::Normal => {
                if self.normal_queue.len() >= self.max_queue_sizes.normal {
                    Err(BraidpoolError::QueueFull {
                        queue_type: "Normal".to_string(),
                    })
                } else {
                    self.normal_queue.push_back(request);
                    self.metrics
                        .queue_size_normal
                        .store(self.normal_queue.len(), Ordering::Relaxed);
                    Ok(())
                }
            }
            RequestPriority::Low => {
                if self.low_queue.len() >= self.max_queue_sizes.low {
                    // Drop oldest low priority request
                    if let Some(dropped) = self.low_queue.pop_front() {
                        self.send_queue_full_error(dropped);
                    }
                }
                self.low_queue.push_back(request);
                self.metrics
                    .queue_size_low
                    .store(self.low_queue.len(), Ordering::Relaxed);
                Ok(())
            }
        };

        if result.is_ok() {
            self.metrics.total_requests.fetch_add(1, Ordering::Relaxed);
        }

        result
    }

    fn send_queue_full_error(&self, dropped_request: BitcoinRequest) {
        match dropped_request {
            BitcoinRequest::IsRecentlySynced { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::RemoveTransaction { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::RemoveMultipleTransactions { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::GetBlockTemplate { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::IsInitialBlockDownload { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
        }
    }

    fn dequeue(&mut self) -> Option<BitcoinRequest> {
        if let Some(request) = self.critical_queue.pop_front() {
            self.metrics
                .queue_size_critical
                .store(self.critical_queue.len(), Ordering::Relaxed);
            return Some(request);
        }

        if let Some(request) = self.high_queue.pop_front() {
            self.metrics
                .queue_size_high
                .store(self.high_queue.len(), Ordering::Relaxed);
            return Some(request);
        }

        if let Some(request) = self.normal_queue.pop_front() {
            self.metrics
                .queue_size_normal
                .store(self.normal_queue.len(), Ordering::Relaxed);
            return Some(request);
        }

        if let Some(request) = self.low_queue.pop_front() {
            self.metrics
                .queue_size_low
                .store(self.low_queue.len(), Ordering::Relaxed);
            return Some(request);
        }

        None
    }

    fn is_overloaded(&self) -> bool {
        self.critical_queue.len() > self.max_queue_sizes.critical / 2
            || self.high_queue.len() > self.max_queue_sizes.high / 2
    }
}

// Notification handler
pub struct BraidpoolNotificationHandler {
    notification_sender: mpsc::UnboundedSender<BitcoinNotification>,
}

impl BraidpoolNotificationHandler {
    fn new(notification_sender: mpsc::UnboundedSender<BitcoinNotification>) -> Self {
        Self {
            notification_sender,
        }
    }
}

impl crate::chain_capnp::chain_notifications::Server for BraidpoolNotificationHandler {
    fn destroy(
        &mut self,
        _: DestroyParams,
        _: DestroyResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        ::capnp::capability::Promise::ok(())
    }

    fn block_connected(
        &mut self,
        params: BlockConnectedParams,
        _: BlockConnectedResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        if let Ok(info) = pry!(params.get()).get_block() {
            let height = info.get_height() as u32;
            let hash = info.get_hash().map(|h| h.to_vec()).unwrap_or_default();
            let notification = BitcoinNotification::BlockConnected { height, hash };
            let _ = self.notification_sender.send(notification);
        }
        ::capnp::capability::Promise::ok(())
    }

    fn transaction_added_to_mempool(
        &mut self,
        _: crate::chain_capnp::chain_notifications::TransactionAddedToMempoolParams,
        _: crate::chain_capnp::chain_notifications::TransactionAddedToMempoolResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        // No-op: We don't want to handle mempool transactions
        ::capnp::capability::Promise::ok(())
    }

    fn transaction_removed_from_mempool(
        &mut self,
        _: crate::chain_capnp::chain_notifications::TransactionRemovedFromMempoolParams,
        _: crate::chain_capnp::chain_notifications::TransactionRemovedFromMempoolResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        // No-op: We don't want to handle mempool transactions
        ::capnp::capability::Promise::ok(())
    }

    fn block_disconnected(
        &mut self,
        _: crate::chain_capnp::chain_notifications::BlockDisconnectedParams,
        _: crate::chain_capnp::chain_notifications::BlockDisconnectedResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        // No-op: We don't need to handle block disconnections
        ::capnp::capability::Promise::ok(())
    }

    fn updated_block_tip(
        &mut self,
        _: UpdatedBlockTipParams,
        _: UpdatedBlockTipResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        let _ = self
            .notification_sender
            .send(BitcoinNotification::UpdatedBlockTip);
        ::capnp::capability::Promise::ok(())
    }

    fn chain_state_flushed(
        &mut self,
        _: ChainStateFlushedParams,
        _: ChainStateFlushedResults,
    ) -> ::capnp::capability::Promise<(), ::capnp::Error> {
        let _ = self
            .notification_sender
            .send(BitcoinNotification::ChainStateFlushed);
        ::capnp::capability::Promise::ok(())
    }
}

// Bitcoin RPC client with both chain and mining interfaces
pub struct BitcoinRpcClient {
    ipc_task: JoinHandle<Result<(), capnp::Error>>,
    chain_interface: ChainClient,
    mining_interface: crate::mining_capnp::mining::Client,
    thread_client: ThreadClient,
    disconnector: capnp_rpc::Disconnector<twoparty::VatId>,
}

impl BitcoinRpcClient {
    pub async fn new(stream: tokio::net::UnixStream) -> Result<Self, Box<dyn std::error::Error>> {
        let (reader, writer) = stream.into_split();
        let network = Box::new(twoparty::VatNetwork::new(
            reader.compat(),
            writer.compat_write(),
            rpc_twoparty_capnp::Side::Client,
            Default::default(),
        ));

        let mut rpc = RpcSystem::new(network, None);
        let init_interface: InitClient = rpc.bootstrap(rpc_twoparty_capnp::Side::Server);
        let disconnector = rpc.get_disconnector();
        let ipc_task = task::spawn_local(rpc.map(|_| Ok(())));

        // Initialize thread map
        let init_req = init_interface.construct_request();
        let response = init_req.send().promise.await?;
        let thread_map = response.get()?.get_thread_map()?;
        let mk_thread_req = thread_map.make_thread_request();
        let response = mk_thread_req.send().promise.await?;
        let thread = response.get()?.get_result()?;

        // Create chain interface
        let mut mk_chain_req = init_interface.make_chain_request();
        mk_chain_req.get().get_context()?.set_thread(thread.clone());
        let response = mk_chain_req.send().promise.await?;
        let chain_interface = response.get()?.get_result()?;

        // Create mining interface
        let mut mk_mining_req = init_interface.make_mining_request();
        mk_mining_req
            .get()
            .get_context()?
            .set_thread(thread.clone());
        let response = mk_mining_req.send().promise.await?;
        let mining_interface = response.get()?.get_result()?;

        Ok(Self {
            ipc_task,
            thread_client: thread,
            chain_interface,
            mining_interface,
            disconnector,
        })
    }

    pub async fn remove_transaction_from_mempool(
        &self,
        txid: &[u8],
    ) -> Result<bool, Box<dyn Error>> {
        let mut delete_req = self.chain_interface.remove_tx_from_mempool_request();
        delete_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let mut reversed_txid = txid.to_vec();
        reversed_txid.reverse();
        delete_req.get().set_txid(&reversed_txid);
        let response = delete_req.send().promise.await?;
        let result = response.get()?;
        Ok(result.get_result())
    }

    pub async fn get_mining_tip_info(&self) -> Result<(u32, Vec<u8>), Box<dyn Error>> {
        let mut tip_req = self.mining_interface.get_tip_request();
        tip_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let response = tip_req.send().promise.await?;
        let tip_result = response.get()?;

        if !tip_result.get_has_result() {
            return Err("Tip information not available".into());
        }
        let block_ref = tip_result.get_result()?;
        let height = block_ref.get_height() as u32;
        let hash = block_ref.get_hash()?.to_vec();

        Ok((height, hash))
    }

    pub async fn get_block_timestamp_by_height(&self, height: u32) -> Result<u64, Box<dyn Error>> {
        let mut hash_req = self.chain_interface.get_block_hash_request();
        hash_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        hash_req.get().set_height(height as i32);

        let hash_response = hash_req.send().promise.await?;
        let hash_result = hash_response.get()?;
        if !hash_result.has_result() {
            return Err(format!("Block hash at height {} not found", height).into());
        }
        let block_hash = hash_result.get_result()?.to_vec();
        let mut find_block_req = self.chain_interface.find_block_request();
        find_block_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        find_block_req.get().init_block().set_want_time(true);
        find_block_req.get().set_hash(&block_hash);

        let response = find_block_req.send().promise.await?;
        let block_result = response.get()?;
        if !block_result.get_result() {
            return Err(format!("Block at height {} not found", height).into());
        }
        let found_block = block_result.get_block()?;
        let timestamp = found_block.get_time() as u64;
        Ok(timestamp)
    }

    pub async fn is_recently_synced(&self) -> Result<bool, Box<dyn Error>> {
        let ibd = self.is_initial_block_download().await?;
        if ibd {
            log::info!("Node is in initial block download - not synced");
            return Ok(false);
        }
        let (tip_height, _tip_hash) = match self.get_mining_tip_info().await {
            Ok(info) => info,
            Err(e) => {
                log::warn!("Failed to get mining tip info: {} - aborting", e);
                return Ok(false); // If we can't get tip but not in IBD, abort
            }
        };
        let tip_timestamp = match self.get_block_timestamp_by_height(tip_height).await {
            Ok(timestamp) => timestamp,
            Err(e) => {
                log::warn!(
                    "Failed to get timestamp for block #{}: {} - using IBD check only",
                    tip_height,
                    e
                );
                return Ok(false); // If we can't get timestamp but not in IBD, abort
            }
        };
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        let time_diff_seconds = now.saturating_sub(tip_timestamp);
        let time_diff_minutes = time_diff_seconds / 60;

        // Consider synced if latest block is within 150 minutes (worst case 2.5 hours)
        let is_recent = time_diff_seconds < 9000;
        log::info!(
            "Sync check - Block #{}, timestamp: {}, now: {}, diff: {}min, synced: {}",
            tip_height,
            tip_timestamp,
            now,
            time_diff_minutes,
            is_recent
        );

        Ok(is_recent)
    }

    pub async fn is_initial_block_download(&self) -> Result<bool, Box<dyn Error>> {
        let mut ibd_req = self.chain_interface.is_initial_block_download_request();
        ibd_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let response = ibd_req.send().promise.await?;
        let result = response.get()?;
        Ok(result.get_result())
    }

    pub async fn get_block_template(
        &self,
        _rules: Option<Vec<String>>,
    ) -> Result<Vec<u8>, Box<dyn Error>> {
        let mut create_block_req = self.mining_interface.create_new_block_request();
        let mut options = create_block_req.get().init_options();
        options.set_block_reserved_weight(4000);
        options.set_use_mempool(true);
        let response = create_block_req.send().promise.await?;
        let block_template_interface = response.get()?.get_result()?;

        let mut block_req = block_template_interface.get_block_request();
        block_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());

        let response = block_req.send().promise.await?;
        let result = response.get()?;
        let template_data = result.get_result()?;

        Ok(template_data.to_vec())
    }

    pub async fn register_notifications(
        &self,
        notification_sender: mpsc::UnboundedSender<BitcoinNotification>,
    ) -> Result<(), Box<dyn Error>> {
        let notif_handler =
            capnp_rpc::new_client(BraidpoolNotificationHandler::new(notification_sender));
        let mut register_req = self.chain_interface.handle_notifications_request();
        register_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        register_req.get().set_notifications(notif_handler);
        register_req.send().promise.await?;
        Ok(())
    }

    pub async fn disconnect(self) -> Result<(), capnp::Error> {
        self.disconnector.await?;
        self.ipc_task
            .await
            .map_err(|e| capnp::Error::failed(format!("Task join error: {}", e)))??;
        Ok(())
    }
}

#[derive(Debug)]
pub struct QueuedRequest {
    request: BitcoinRequest,
    enqueue_time: Instant,
}

#[derive(Debug, Clone)]
pub struct ClientConfig {
    pub queue_limits: QueueLimits,
    pub metrics_interval_secs: u64,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            queue_limits: QueueLimits::default(),
            metrics_interval_secs: 60,
        }
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct QueueStats {
    pub failed_requests: usize,
    pub pending_requests: usize,
    pub avg_processing_time_ms: usize,
    pub queue_sizes: QueueSizeStats,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct QueueSizeStats {
    pub critical: usize,
    pub high: usize,
    pub normal: usize,
    pub low: usize,
}

pub struct SharedBitcoinClient {
    request_sender: mpsc::UnboundedSender<QueuedRequest>,
    notification_receiver: Option<mpsc::UnboundedReceiver<BitcoinNotification>>,
    processor_task: Option<JoinHandle<()>>,
    shutdown_sender: Option<mpsc::UnboundedSender<()>>,
    metrics: Arc<QueueMetrics>,
}

impl SharedBitcoinClient {
    pub async fn new(socket_path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        Self::new_with_config(socket_path, ClientConfig::default()).await
    }

    pub async fn new_with_config(
        socket_path: &str,
        config: ClientConfig,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let (request_sender, mut request_receiver) = mpsc::unbounded_channel::<QueuedRequest>();
        let (notification_sender, internal_notification_receiver) = mpsc::unbounded_channel();
        let (external_notification_sender, external_notification_receiver) =
            mpsc::unbounded_channel();
        let (shutdown_sender, mut shutdown_receiver) = mpsc::unbounded_channel();

        let stream = UnixStream::connect(socket_path).await?;
        let bitcoin_client = BitcoinRpcClient::new(stream).await?;
        bitcoin_client
            .register_notifications(notification_sender)
            .await?;

        let metrics = Arc::new(QueueMetrics::default());
        let queue_limits = config.queue_limits.clone();

        let processor_task = tokio::task::spawn_local({
            let metrics = metrics.clone();
            let config = config.clone();

            async move {
                let mut priority_queue = PriorityRequestQueue::new(queue_limits, metrics.clone());
                let mut notification_receiver = internal_notification_receiver;
                let external_notification_sender = Some(external_notification_sender);
                let mut metrics_interval =
                    tokio::time::interval(Duration::from_secs(config.metrics_interval_secs));

                loop {
                    tokio::select! {
                        _ = shutdown_receiver.recv() => break,

                        queued_request = request_receiver.recv() => {
                            if let Some(QueuedRequest { request, enqueue_time}) = queued_request {
                                let queue_wait_time = enqueue_time.elapsed();
                                if queue_wait_time > Duration::from_millis(100) {
                                    log::warn!("Request spent {:?} in queue before processing", queue_wait_time);
                                }
                                if let Err(e) = priority_queue.enqueue(request) {
                                    eprintln!("Failed to enqueue request: {}", e);
                                }
                                // Process immediately if critical or high priority
                                while let Some(next_request) = priority_queue.dequeue() {
                                    let processing_start = Instant::now();
                                    Self::process_single_request(&bitcoin_client, next_request).await;
                                    let total_time = enqueue_time.elapsed();
                                    let processing_time = processing_start.elapsed();
                                    let actual_queue_time = total_time.saturating_sub(processing_time);
                                    metrics.processed_requests.fetch_add(1, Ordering::Relaxed);
                                    let processing_time_ms = processing_time.as_millis() as usize;
                                    let current_avg = metrics.avg_processing_time_ms.load(Ordering::Relaxed);
                                    let new_avg = if current_avg == 0 {
                                        processing_time_ms
                                    } else {
                                        (current_avg * 9 + processing_time_ms) / 10
                                    };
                                    metrics.avg_processing_time_ms.store(new_avg, Ordering::Relaxed);
                                    if total_time > Duration::from_millis(1000) {
                                        log::warn!("Slow request: queue_time={:?}, processing_time={:?}, total_time={:?}",
                                        actual_queue_time, processing_time, total_time);
                                    }
                                }
                            } else {
                                break;
                            }
                        }

                        notification = notification_receiver.recv() => {
                            match notification {
                                Some(notif) => {
                                    if let Some(ref sender) = external_notification_sender {
                                        if sender.send(notif).is_err() {
                                            break;
                                        }
                                    }
                                }
                                None => {
                                    if let Some(ref sender) = external_notification_sender {
                                        let _ = sender.send(BitcoinNotification::ConnectionLost {
                                            reason: "Notification channel closed".to_string()
                                        });
                                    }
                                    break;
                                }
                            }
                        }

                        _ = metrics_interval.tick() => {
                            Self::report_metrics(&metrics, &priority_queue);
                        }
                    }
                }

                let _ = bitcoin_client.disconnect().await;
            }
        });

        Ok(Self {
            request_sender,
            notification_receiver: Some(external_notification_receiver),
            processor_task: Some(processor_task),
            shutdown_sender: Some(shutdown_sender),
            metrics,
        })
    }

    async fn process_single_request(bitcoin_client: &BitcoinRpcClient, request: BitcoinRequest) {
        let processing_start = Instant::now();
        match request {
            BitcoinRequest::IsRecentlySynced { response, .. } => {
                match bitcoin_client.is_recently_synced().await {
                    Ok(is_synced) => {
                        let _ = response.send(Ok(is_synced));
                    }
                    Err(e) => {
                        let _ = response.send(Err(e.to_string()));
                    }
                }
            }
            BitcoinRequest::IsInitialBlockDownload { response, .. } => {
                match bitcoin_client.is_initial_block_download().await {
                    Ok(is_ibd) => {
                        let _ = response.send(Ok(is_ibd));
                    }
                    Err(e) => {
                        let _ = response.send(Err(e.to_string()));
                    }
                }
            }
            BitcoinRequest::RemoveTransaction { txid, response, .. } => {
                match bitcoin_client.remove_transaction_from_mempool(&txid).await {
                    Ok(removed) => {
                        let _ = response.send(Ok(removed));
                    }
                    Err(e) => {
                        let _ = response.send(Err(e.to_string()));
                    }
                }
            }

            BitcoinRequest::GetBlockTemplate {
                rules, response, ..
            } => match bitcoin_client.get_block_template(rules).await {
                Ok(template) => {
                    let _ = response.send(Ok(template));
                }
                Err(e) => {
                    let _ = response.send(Err(e.to_string()));
                }
            },
            BitcoinRequest::RemoveMultipleTransactions {
                txids, response, ..
            } => {
                let mut results = Vec::new();

                for txid in txids {
                    match bitcoin_client.remove_transaction_from_mempool(&txid).await {
                        Ok(removed) => {
                            results.push((txid, removed));
                        }
                        Err(_) => {
                            results.push((txid, false));
                        }
                    }
                }
                let _ = response.send(Ok(results));
            }
        }

        let processing_time = processing_start.elapsed();
        if processing_time > Duration::from_millis(500) {
            log::warn!("Slow request processing: {:?}", processing_time);
        }
    }

    pub fn get_queue_stats(&self) -> QueueStats {
        let total = self.metrics.total_requests.load(Ordering::Acquire);
        let processed = self.metrics.processed_requests.load(Ordering::Acquire);
        let failed = self.metrics.failed_requests.load(Ordering::Acquire);
        let pending = total.saturating_sub(processed);
        QueueStats {
            failed_requests: failed,
            pending_requests: pending,
            avg_processing_time_ms: self.metrics.avg_processing_time_ms.load(Ordering::Acquire),
            queue_sizes: QueueSizeStats {
                critical: self.metrics.queue_size_critical.load(Ordering::Relaxed),
                high: self.metrics.queue_size_high.load(Ordering::Relaxed),
                normal: self.metrics.queue_size_normal.load(Ordering::Relaxed),
                low: self.metrics.queue_size_low.load(Ordering::Relaxed),
            },
        }
    }

    pub fn is_healthy(&self) -> bool {
        let stats = self.get_queue_stats();
        stats.pending_requests < 100
            && stats.avg_processing_time_ms < 1000
            && stats.queue_sizes.critical < 50
    }

    pub async fn is_recently_synced(
        &self,
        priority: Option<RequestPriority>,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();
        let request = BitcoinRequest::IsRecentlySynced {
            response: response_sender,
            priority: priority.unwrap_or(RequestPriority::High),
        };
        self.request_sender.send(QueuedRequest {
            request,
            enqueue_time: Instant::now(),
        })?;
        let result = response_receiver.await??;
        Ok(result)
    }

    pub async fn get_block_template(
        &self,
        rules: Option<Vec<String>>,
        priority: Option<RequestPriority>,
    ) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = BitcoinRequest::GetBlockTemplate {
            rules,
            response: response_sender,
            priority: priority.unwrap_or(RequestPriority::Critical),
        };

        self.request_sender.send(QueuedRequest {
            request,
            enqueue_time: Instant::now(),
        })?;

        let result = response_receiver.await??;
        Ok(result)
    }

    pub async fn is_initial_block_download(
        &self,
        priority: Option<RequestPriority>,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();
        let request = BitcoinRequest::IsInitialBlockDownload {
            response: response_sender,
            priority: priority.unwrap_or(RequestPriority::High),
        };
        self.request_sender.send(QueuedRequest {
            request,
            enqueue_time: Instant::now(),
        })?;
        let result = response_receiver.await??;
        Ok(result)
    }

    pub fn report_metrics(metrics: &QueueMetrics, queue: &PriorityRequestQueue) {
        let total = metrics.total_requests.load(Ordering::Relaxed);
        let processed = metrics.processed_requests.load(Ordering::Relaxed);
        let failed = metrics.failed_requests.load(Ordering::Relaxed);
        let pending = total.saturating_sub(processed);

        if pending > 50 || queue.is_overloaded() {
            log::debug!(
                "Queue: {} pending, {} failed, avg: {}ms{}",
                pending,
                failed,
                metrics.avg_processing_time_ms.load(Ordering::Relaxed),
                if queue.is_overloaded() {
                    " [OVERLOADED]"
                } else {
                    ""
                }
            );
        }
    }

    pub async fn shutdown(mut self) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(shutdown_sender) = self.shutdown_sender.take() {
            let _ = shutdown_sender.send(());
        }

        if let Some(task) = self.processor_task.take() {
            let _ = task.await;
        }

        Ok(())
    }

    // Used to remove a single transaction from the mempool
    #[allow(dead_code)]
    pub async fn remove_transaction(
        &self,
        txid: &[u8],
        priority: Option<RequestPriority>,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = BitcoinRequest::RemoveTransaction {
            txid: txid.to_vec(),
            response: response_sender,
            priority: priority.unwrap_or(RequestPriority::Normal),
        };

        self.request_sender.send(QueuedRequest {
            request,
            enqueue_time: Instant::now(),
        })?;

        let result = response_receiver.await??;
        Ok(result)
    }

    // Used to remove multiple transactions from the mempool
    #[allow(dead_code)]
    pub async fn remove_multiple_transactions(
        &self,
        txids: Vec<Vec<u8>>,
    ) -> Result<Vec<(Vec<u8>, bool)>, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = BitcoinRequest::RemoveMultipleTransactions {
            txids,
            response: response_sender,
            priority: RequestPriority::High,
        };

        self.request_sender.send(QueuedRequest {
            request,
            enqueue_time: Instant::now(),
        })?;

        let result = response_receiver.await??;
        Ok(result)
    }

    pub fn take_notification_receiver(
        &mut self,
    ) -> Option<mpsc::UnboundedReceiver<BitcoinNotification>> {
        self.notification_receiver.take()
    }
}
