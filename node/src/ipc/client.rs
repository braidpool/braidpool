use crate::error::BraidpoolError;
use crate::init_capnp::init::Client as InitClient;
use crate::proxy_capnp::thread::Client as ThreadClient;
use capnp_rpc::{rpc_twoparty_capnp, twoparty, RpcSystem};
use futures::FutureExt;
use std::collections::VecDeque;
use std::error::Error;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::vec;
use tokio::net::UnixStream;
use tokio::sync::{mpsc, oneshot};
use tokio::task::{self, JoinHandle};
use tokio_util::compat::{TokioAsyncReadCompatExt, TokioAsyncWriteCompatExt};

pub fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>()
}

#[derive(Debug, Clone)]
pub struct CheckBlockResult {
    pub reason: String,
    pub debug: String,
    pub result: bool,
}

#[derive(Debug, Clone)]
pub struct BlockTemplateComponents {
    pub header: Vec<u8>,
    pub coinbase_transaction: Vec<u8>,
    pub fees: Vec<u64>,
    pub coinbase_merkle_path: Vec<Vec<u8>>,
    pub coinbase_commitment: Vec<u8>,
    pub block_hex: Vec<u8>,
}

// Bitcoin notification events
#[derive(Debug, Clone)]
pub enum BitcoinNotification {
    TipChanged { height: u32, hash: Vec<u8> },
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
    GetBlockTemplateComponents {
        rules: Option<Vec<String>>,
        response: oneshot::Sender<Result<BlockTemplateComponents, String>>,
        priority: RequestPriority,
    },
    IsInitialBlockDownload {
        response: oneshot::Sender<Result<bool, String>>,
        priority: RequestPriority,
    },
    GetMiningTipInfo {
        response: oneshot::Sender<Result<(u32, Vec<u8>), String>>,
        priority: RequestPriority,
    },
    CheckBlock {
        block_data: Vec<u8>,
        check_merkle_root: bool,
        check_pow: bool,
        response: oneshot::Sender<Result<CheckBlockResult, String>>,
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
            BitcoinRequest::RemoveTransaction { priority, .. } => *priority,
            BitcoinRequest::RemoveMultipleTransactions { priority, .. } => *priority,
            BitcoinRequest::GetBlockTemplate { priority, .. } => *priority,
            BitcoinRequest::GetBlockTemplateComponents { priority, .. } => *priority,
            BitcoinRequest::IsInitialBlockDownload { priority, .. } => *priority,
            BitcoinRequest::CheckBlock { priority, .. } => *priority,
            BitcoinRequest::GetMiningTipInfo { priority, .. } => *priority,
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
            BitcoinRequest::RemoveTransaction { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::RemoveMultipleTransactions { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::GetBlockTemplate { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::GetBlockTemplateComponents { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::IsInitialBlockDownload { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::CheckBlock { response, .. } => {
                let _ = response.send(Err("Queue full - request dropped".to_string()));
            }
            BitcoinRequest::GetMiningTipInfo { response, .. } => {
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

// Bitcoin RPC client with both chain and mining interfaces
pub struct BitcoinRpcClient {
    ipc_task: JoinHandle<Result<(), capnp::Error>>,
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
            mining_interface,
            disconnector,
        })
    }

    pub async fn remove_transaction_from_mempool(
        &self,
        txid: &[u8],
    ) -> Result<bool, Box<dyn Error>> {
        let mut delete_req = self.mining_interface.remove_tx_from_mempool_request();
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

    pub async fn is_initial_block_download(&self) -> Result<bool, Box<dyn Error>> {
        let mut ibd_req = self.mining_interface.is_initial_block_download_request();
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

    pub async fn get_block_template_components(
        &self,
        _rules: Option<Vec<String>>,
    ) -> Result<BlockTemplateComponents, Box<dyn Error>> {
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
        let block_response = block_req.send().promise.await?;
        let full_block_data = block_response.get()?.get_result()?.to_vec();

        let mut header_req = block_template_interface.get_block_header_request();
        header_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let header_response = header_req.send().promise.await?;
        let header_data = header_response.get()?.get_result()?.to_vec();

        let mut coinbase_req = block_template_interface.get_coinbase_tx_request();
        coinbase_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let coinbase_response = coinbase_req.send().promise.await?;
        let coinbase_data = coinbase_response.get()?.get_result()?.to_vec();

        let mut fees_req = block_template_interface.get_tx_fees_request();
        fees_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let fees_response = fees_req.send().promise.await?;
        let fees_result = fees_response.get()?;
        let fees_list = fees_result.get_result()?;
        let mut fees_vec = Vec::new();
        let mut fees_total: u64 = 0;
        for i in 0..fees_list.len() {
            let fee_value = fees_list.get(i);
            fees_total = fees_total + fee_value as u64;
            fees_vec.push(fee_value as u64);
        }

        let mut merkle_path_req = block_template_interface.get_coinbase_merkle_path_request();
        merkle_path_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let merkle_path_response = merkle_path_req.send().promise.await?;
        let merkle_path_result = merkle_path_response.get()?;
        let merkle_list = merkle_path_result.get_result()?;

        let mut coinbase_merkle_path = Vec::new();
        for i in 0..merkle_list.len() {
            match merkle_list.get(i) {
                Ok(hash_data) => {
                    let hash_bytes = hash_data.to_vec();
                    coinbase_merkle_path.push(hash_bytes);
                }
                Err(e) => {
                    log::error!("Failed to get merkle[{}]: {}", i, e);
                    break;
                }
            }
        }

        let mut commitment_req = block_template_interface.get_coinbase_commitment_request();
        commitment_req
            .get()
            .get_context()?
            .set_thread(self.thread_client.clone());
        let commitment_response = commitment_req.send().promise.await?;
        let commitment_data = commitment_response.get()?.get_result()?.to_vec();

        Ok(BlockTemplateComponents {
            header: header_data,
            coinbase_transaction: coinbase_data,
            fees: fees_vec,
            coinbase_merkle_path,
            coinbase_commitment: commitment_data,
            block_hex: full_block_data,
        })
    }

    pub async fn check_block(
        &self,
        block_data: &[u8],
        check_merkle_root: bool,
        check_pow: bool,
    ) -> Result<CheckBlockResult, Box<dyn Error>> {
        let mut check_block_req = self.mining_interface.check_block_request();

        check_block_req.get().set_block(block_data);

        let mut options = check_block_req.get().init_options();
        options.set_check_merkle_root(check_merkle_root);
        options.set_check_pow(check_pow);

        let response = check_block_req.send().promise.await?;
        let result = response.get()?;

        let reason = result.get_reason()?.to_string().unwrap_or_default();
        let debug = result.get_debug()?.to_string().unwrap_or_default();
        let check_result = result.get_result();

        Ok(CheckBlockResult {
            reason,
            debug,
            result: check_result,
        })
    }

    pub async fn wait_for_tip_change(
        &self,
        mut current_tip: Vec<u8>,
        timeout: f64,
        notification_sender: mpsc::UnboundedSender<BitcoinNotification>,
    ) -> Result<(), Box<dyn Error>> {
        loop {
            let mut wait_req = self.mining_interface.wait_tip_changed_request();
            wait_req
                .get()
                .get_context()?
                .set_thread(self.thread_client.clone());
            wait_req.get().set_current_tip(&current_tip);
            wait_req.get().set_timeout(timeout);

            match wait_req.send().promise.await {
                Ok(response) => {
                    let result = response.get()?;
                    let new_tip = result.get_result()?;
                    let height = new_tip.get_height() as u32;
                    let hash = new_tip.get_hash()?.to_vec();

                    if hash != current_tip {
                        let notification = BitcoinNotification::TipChanged {
                            height,
                            hash: hash.clone(),
                        };
                        if let Err(e) = notification_sender.send(notification) {
                            log::error!("Failed to send tip change notification: {}", e);
                            if notification_sender.is_closed() {
                                log::error!("Notification channel closed, stopping tip monitoring");
                                return Err("Notification channel closed".into());
                            }
                        }
                        current_tip = hash;
                    } else {
                        log::debug!("waitTipChanged returned same tip, maybe a timeout)");
                    }
                }
                Err(e) => {
                    log::error!("waitTipChanged failed: {}", e);
                    let _ = notification_sender.send(BitcoinNotification::ConnectionLost {
                        reason: format!("waitTipChanged error: {}", e),
                    });
                    return Err(Box::new(e));
                }
            }
        }
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
    tip_watcher_task: Option<JoinHandle<()>>,
    shutdown_sender: Option<mpsc::UnboundedSender<()>>,
    tip_shutdown_sender: Option<mpsc::UnboundedSender<()>>,
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
        let (notification_sender, mut internal_notification_receiver) = mpsc::unbounded_channel();
        let (external_notification_sender, external_notification_receiver) =
            mpsc::unbounded_channel();
        let (shutdown_sender, mut shutdown_receiver) = mpsc::unbounded_channel();

        let temp_stream = UnixStream::connect(socket_path).await?;
        let temp_client = BitcoinRpcClient::new(temp_stream).await?;
        let (_, initial_tip_hash) = temp_client
            .get_mining_tip_info()
            .await
            .unwrap_or((0, vec![]));
        temp_client.disconnect().await?;

        let metrics = Arc::new(QueueMetrics::default());
        let queue_limits = config.queue_limits.clone();
        let (tip_shutdown_sender, mut tip_shutdown_receiver) = mpsc::unbounded_channel::<()>();

        let tip_watcher_task = tokio::task::spawn_local({
            let socket_path = socket_path.to_string();
            let notification_sender_clone = notification_sender.clone();
            let initial_tip_hash = initial_tip_hash;

            async move {
                let watcher_stream = match UnixStream::connect(&socket_path).await {
                    Ok(stream) => stream,
                    Err(e) => {
                        log::error!("Failed to connect tip watcher: {}", e);
                        return;
                    }
                };

                let bitcoin_client = match BitcoinRpcClient::new(watcher_stream).await {
                    Ok(client) => client,
                    Err(e) => {
                        log::error!("Failed to create tip watcher client: {}", e);
                        return;
                    }
                };

                let _result = tokio::select! {
                    _ = tip_shutdown_receiver.recv() => {
                        log::info!("Tip watcher received shutdown signal");
                        Ok(())
                    }
                    result = bitcoin_client.wait_for_tip_change(
                        initial_tip_hash,
                        1728000.0, // 8 hours
                        notification_sender_clone.clone(),
                    ) => {
                        if let Err(e) = &result {
                            log::error!("Tip watcher failed: {}", e);
                            let _ = notification_sender_clone.send(BitcoinNotification::ConnectionLost {
                                reason: format!("Tip watcher error: {}", e),
                            });
                        }
                        result
                    }
                };

                // Always cleanup bitcoin client
                if let Err(e) = bitcoin_client.disconnect().await {
                    log::error!("Error disconnecting tip watcher bitcoin client: {}", e);
                }
            }
        });

        let processor_task = tokio::task::spawn_local({
            let socket_path = socket_path.to_string();
            let metrics = metrics.clone();
            let config = config.clone();

            async move {
                let processor_stream = match UnixStream::connect(&socket_path).await {
                    Ok(stream) => stream,
                    Err(e) => {
                        log::error!("Failed to connect processor: {}", e);
                        return;
                    }
                };

                let bitcoin_client = match BitcoinRpcClient::new(processor_stream).await {
                    Ok(client) => client,
                    Err(e) => {
                        log::error!("Failed to create processor client: {}", e);
                        return;
                    }
                };

                let mut priority_queue = PriorityRequestQueue::new(queue_limits, metrics.clone());
                let external_notification_sender = Some(external_notification_sender);
                let mut metrics_interval =
                    tokio::time::interval(Duration::from_secs(config.metrics_interval_secs));

                loop {
                    tokio::select! {
                        _ = shutdown_receiver.recv() => {
                            log::info!("Processor received shutdown signal");
                            break;
                        }

                        queued_request = request_receiver.recv() => {
                            if let Some(QueuedRequest { request, enqueue_time}) = queued_request {
                                let queue_wait_time = enqueue_time.elapsed();
                                if queue_wait_time > Duration::from_millis(100) {
                                    log::warn!("Request spent {:?} in queue before processing", queue_wait_time);
                                }
                                if let Err(e) = priority_queue.enqueue(request) {
                                    log::error!("Failed to enqueue request: {}", e);
                                }
                                // Process all queued requests
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
                                log::info!("Request receiver closed, processor shutting down");
                                break;
                            }
                        }

                        notification = internal_notification_receiver.recv() => {
                            match notification {
                                Some(notif) => {
                                    if let Some(ref sender) = external_notification_sender {
                                        if let Err(e) = sender.send(notif) {
                                            log::error!("Failed to forward notification to external receiver: {}", e);
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

                // Always cleanup bitcoin client
                if let Err(e) = bitcoin_client.disconnect().await {
                    log::error!("Error disconnecting processor bitcoin client: {}", e);
                }
            }
        });

        Ok(Self {
            request_sender,
            notification_receiver: Some(external_notification_receiver),
            processor_task: Some(processor_task),
            tip_watcher_task: Some(tip_watcher_task),
            shutdown_sender: Some(shutdown_sender),
            tip_shutdown_sender: Some(tip_shutdown_sender),
            metrics,
        })
    }

    async fn process_single_request(bitcoin_client: &BitcoinRpcClient, request: BitcoinRequest) {
        let processing_start = Instant::now();
        match request {
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
            BitcoinRequest::GetBlockTemplateComponents {
                rules, response, ..
            } => match bitcoin_client.get_block_template_components(rules).await {
                Ok(components) => {
                    let _ = response.send(Ok(components));
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
            BitcoinRequest::GetMiningTipInfo { response, .. } => {
                match bitcoin_client.get_mining_tip_info().await {
                    Ok(info) => {
                        let _ = response.send(Ok(info));
                    }
                    Err(e) => {
                        let _ = response.send(Err(e.to_string()));
                    }
                }
            }
            BitcoinRequest::CheckBlock {
                block_data,
                check_merkle_root,
                check_pow,
                response,
                ..
            } => {
                match bitcoin_client
                    .check_block(&block_data, check_merkle_root, check_pow)
                    .await
                {
                    Ok(check_result) => {
                        let _ = response.send(Ok(check_result));
                    }
                    Err(e) => {
                        let _ = response.send(Err(e.to_string()));
                    }
                }
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

    pub async fn get_block_template(
        &self,
        rules: Option<Vec<String>>,
        priority: Option<RequestPriority>,
    ) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = BitcoinRequest::GetBlockTemplate {
            rules,
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

    pub async fn get_block_template_components(
        &self,
        rules: Option<Vec<String>>,
        priority: Option<RequestPriority>,
    ) -> Result<BlockTemplateComponents, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = BitcoinRequest::GetBlockTemplateComponents {
            rules,
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

    pub async fn get_mining_tip_info(
        &self,
        priority: Option<RequestPriority>,
    ) -> Result<(u32, Vec<u8>), Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();
        let request = BitcoinRequest::GetMiningTipInfo {
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

    pub async fn check_block(
        &self,
        block_data: Vec<u8>,
        check_merkle_root: bool,
        check_pow: bool,
        priority: Option<RequestPriority>,
    ) -> Result<CheckBlockResult, Box<dyn std::error::Error>> {
        let (response_sender, response_receiver) = oneshot::channel();

        let request = BitcoinRequest::CheckBlock {
            block_data,
            check_merkle_root,
            check_pow,
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

    pub fn take_notification_receiver(
        &mut self,
    ) -> Option<mpsc::UnboundedReceiver<BitcoinNotification>> {
        self.notification_receiver.take()
    }

    pub async fn shutdown(mut self) -> Result<(), Box<dyn std::error::Error>> {
        // Send shutdown signals
        if let Some(shutdown_sender) = self.shutdown_sender.take() {
            let _ = shutdown_sender.send(());
        }

        if let Some(tip_shutdown_sender) = self.tip_shutdown_sender.take() {
            let _ = tip_shutdown_sender.send(());
        }

        // Wait for tasks to complete gracefully
        if let Some(task) = self.processor_task.take() {
            if let Err(e) = task.await {
                log::error!("Processor task join error: {}", e);
            }
        }

        if let Some(tip_task) = self.tip_watcher_task.take() {
            if let Err(e) = tip_task.await {
                log::error!("Tip watcher task join error: {}", e);
            }
        }
        log::info!("SharedBitcoinClient shutdown complete");
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
}

impl Drop for SharedBitcoinClient {
    fn drop(&mut self) {
        // Send shutdown signals to both processor and tip-watcher
        if let Some(shutdown_sender) = self.shutdown_sender.take() {
            let _ = shutdown_sender.send(());
        }
        if let Some(tip_shutdown_sender) = self.tip_shutdown_sender.take() {
            let _ = tip_shutdown_sender.send(());
        }

        // Abort tasks if they're still running
        if let Some(task) = self.processor_task.take() {
            if !task.is_finished() {
                task.abort();
            }
        }
        if let Some(tip_task) = self.tip_watcher_task.take() {
            if !tip_task.is_finished() {
                tip_task.abort();
            }
        }
    }
}
