//! Listens for block notifications and fetches new block templates via IPC
use crate::config::CoinbaseConfig;
use crate::error::CoinbaseError;
use crate::error::{classify_error, ErrorKind};
use crate::template_creator::{create_block_template, FinalTemplate};
use crate::{TemplateId, MAX_CACHED_TEMPLATES};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::mpsc::Sender;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};
pub mod client;
use bitcoin::Network;
pub use client::{
    BitcoinNotification, BlockTemplateComponents, CheckBlockResult, RequestPriority,
    SharedBitcoinClient,
};

const MAX_BACKOFF: u64 = 300;

/// Main IPC block listener that maintains connection to Bitcoin Core and forwards block templates
///
/// This function implements a robust connection loop that:
/// * Automatically reconnects on connection failures
/// * Fetches initial block template on startup (if node is synced)
/// * Listens for new block notifications and fetches fresh templates
/// * Provides health monitoring and connection statistics
/// * Handles graceful degradation when Bitcoin Core is not fully synced
pub async fn ipc_block_listener(
    ipc_socket_path: String,
    block_template_tx: Sender<Arc<client::BlockTemplate>>,
    network: Network,
    template_cache: Arc<tokio::sync::Mutex<HashMap<TemplateId, Arc<client::BlockTemplate>>>>,
    mut block_submission_rx: tokio::sync::mpsc::UnboundedReceiver<
        crate::stratum::BlockSubmissionRequest,
    >,
) -> Result<(), Box<dyn std::error::Error>> {
    info!(
        socket = %ipc_socket_path,
        network = %network,
        "IPC block listener started"
    );
    let local = tokio::task::LocalSet::new();
    local.run_until(async move {
        loop {
            let mut health_check_interval = tokio::time::interval(tokio::time::Duration::from_secs(30));
            let mut detailed_stats_interval = tokio::time::interval(tokio::time::Duration::from_secs(100));
            let mut backoff_seconds = 1;
            let mut shared_client = match SharedBitcoinClient::new(&ipc_socket_path).await {
                Ok(client) => {
                    info!(socket = %ipc_socket_path, "IPC connection established");
                    client
                }
                Err(e) => {
                    error!(socket = %ipc_socket_path, error = %e, "Failed to connect to IPC socket");
                    info!(retry_delay_secs = 10, "Retrying IPC connection");
                    tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
                    continue;
                }
            };

            let initial_sync_result = loop {
                match shared_client.is_initial_block_download(Some(RequestPriority::High)).await {
                   Ok(in_ibd) => {
                        if in_ibd {
                            info!(in_ibd = true, "Node in IBD - limited functionality");
                            let result = Ok(false); // Not synced, but continue
                            break result;
                        } else {
                            info!(in_ibd = false, "Node synced and ready");
                            break Ok(true);
                        }
                    }
                    Err(e) => {
                        error!(error = %e, "Initial sync check failed");

                        match classify_error(&e) {
                            ErrorKind::Temporary => {
                                warn!(backoff_secs = %backoff_seconds, error = %e, "Temporary sync check error - retrying");
                                tokio::time::sleep(tokio::time::Duration::from_secs(backoff_seconds)).await;
                                backoff_seconds = std::cmp::min(backoff_seconds * 2, MAX_BACKOFF);
                                continue;
                            }
                            ErrorKind::ConnectionBroken => {
                                error!(error = %e, context = "sync_check", "Connection broken during sync check");
                                break Err(ErrorKind::ConnectionBroken);
                            }
                            ErrorKind::LogicError => {
                                warn!(error = %e, "Unexpected sync check error - continuing");
                                break Ok(false);
                            }
                        }
                    }
                }
            };
            let tip_height = match shared_client.get_mining_tip_info(Some(RequestPriority::High)).await {
                    Ok((height, _hash)) => height,
                    Err(e) => {
                        error!(error = %e, "Failed to get mining tip info");
                        continue;
                    }
            };
            // Handle the result properly
            let is_synced = match initial_sync_result {
                Ok(is_synced) => is_synced,
                Err(ErrorKind::ConnectionBroken) => {
                    continue; // Restart connection loop immediately
                }
                Err(_) => {
                    // Handle other errors
                    false
                }
            };

            // Only try to get initial template if node is synced
            if is_synced {
                match get_template_with_retry(
                    &mut shared_client,
                    3,
                    RequestPriority::High,
                    "initial template",
                    tip_height,
                    0,
                    network,
                ).await {
                    Ok(template) => {
                        if let Err(e) = block_template_tx.send(Arc::new(template)).await {
                            error!(error = %e, "Failed to send initial template");
                            continue;
                        }
                    }
                    Err(e) => {
                        error!(error = %e, "Failed to get initial template");
                        match classify_error(&e) {
                            ErrorKind::ConnectionBroken => {
                                error!(
                                    socket = %ipc_socket_path,
                                    operation = "get_template",
                                    "Connection lost - reconnecting"
                                );
                                continue; // Restart connection loop
                            }
                            ErrorKind::Temporary | ErrorKind::LogicError => {
                                warn!(error = %e, "Non-connection error - continuing");
                                // Continue anyway - we'll get templates on block changes
                            }
                        }
                    }
                }
            }

            let mut notification_receiver = match shared_client.take_notification_receiver() {
                Some(receiver) => receiver,
                None => {
                    error!(socket = %ipc_socket_path, "Failed to get notification receiver - reconnecting");
                    tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
                    continue;
                }
            };

            info!(socket = %ipc_socket_path, "Listening for block notifications");

            // Listen for block connect notifications only
            let should_reconnect = loop {
                tokio::select! {
                    notification = notification_receiver.recv() => {
                        match notification {
                            Some(BitcoinNotification::TipChanged { height, hash, .. }) => {
                                let mut hash_reversed = hash.clone();
                                hash_reversed.reverse();
                                info!(
                                    height = height,
                                    hash = %hex::encode(&hash_reversed),
                                    "New block"
                                );
                                match shared_client.is_initial_block_download(Some(RequestPriority::High)).await {
                                    Ok(in_ibd) => {
                                        if !in_ibd { // Node is synced (not in IBD)
                                            match get_template_with_retry(
                                                &mut shared_client,
                                                2,
                                                RequestPriority::High,
                                                &format!("block {}", height),
                                                height,
                                                0,
                                                network,
                                            ).await {
                                                Ok(template) => {
                                                    if let Err(e) = block_template_tx.send(Arc::new(template)).await {
                                                        error!(error = %e, height = height, "Failed to send template");
                                                        break true;
                                                    }
                                                }
                                                Err(e) => {
                                                    error!(error = %e, height = height, "Failed to get block template");
                                                    match classify_error(&e) {
                                                        ErrorKind::ConnectionBroken => {
                                                            error!(
                                                                height = height,
                                                                socket = %ipc_socket_path,
                                                                operation = "get_template",
                                                                "Connection lost - restarting"
                                                            );
                                                            break true;
                                                        }
                                                        ErrorKind::Temporary => {
                                                            warn!(error = %e, height = height, "Non-critical template error - will retry");
                                                        }
                                                        ErrorKind::LogicError => {
                                                            warn!(error = %e, height = height, "Unexpected template error - continuing");
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            warn!(height = height, in_ibd = true, "Node in IBD - skipping template");
                                        }
                                    }
                                    Err(e) => {
                                        error!(error = %e, height = height, "Sync check failed");
                                        match classify_error(&e) {
                                            ErrorKind::ConnectionBroken => {
                                                error!(
                                    socket = %ipc_socket_path,
                                    operation = "sync_check",
                                    "Connection lost during sync check"
                                );
                                                break true;
                                            }
                                            ErrorKind::Temporary => {
                                                warn!(error = %e, height = height, "Non-critical sync error - will retry");
                                            }
                                            ErrorKind::LogicError => {
                                                warn!(error = %e, height = height, "Unexpected sync error - continuing");
                                            }
                                        }
                                    }
                                }
                            }

                            Some(BitcoinNotification::ConnectionLost { reason }) => {
                                error!(reason = %reason, "Connection lost");
                                break true;
                            }

                            None => {
                                error!(context = "notification_receiver", reason = "channel_closed", "Failed to receive notifications - connection lost");
                                break true;
                            }
                        }
                    }

                    submission = block_submission_rx.recv() => {
                    if let Some(submission) = submission {
                        let crate::stratum::BlockSubmissionRequest {
                            template_id,
                            header,
                            coinbase_transaction,
                        } = submission;
                        let block_hash = header.block_hash();
                        let template_opt = template_cache.lock().await.get(&template_id).cloned();

                        if let Some(ipc_template) = template_opt {
                            match shared_client
                                .submit_solution(
                                    ipc_template,
                                    header,
                                    bitcoin::consensus::encode::serialize(&coinbase_transaction),
                                    template_id,
                                    Some(RequestPriority::Critical),
                                )
                                .await
                            {
                                Ok(result) => {
                                    if result.success {
                                        info!(
                                            template_id = %template_id,
                                            block_hash = %block_hash,
                                            "Block ACCEPTED by Bitcoin Core"
                                        );
                                    } else {
                                        error!(
                                            template_id = %template_id,
                                            block_hash = %block_hash,
                                            reason = %result.reason,
                                            "Block REJECTED by Bitcoin Core"
                                        );
                                    }
                                }
                                Err(e) => {
                                    error!(
                                        template_id = %template_id,
                                        block_hash = %block_hash,
                                        error = %e,
                                        "Failed to submit block"
                                    );
                                }
                            }
                        } else {
                            // This represents a potentially valid Bitcoin block that cannot be submitted!
                            // Possible causes:
                            // - Template expired (cache is full and old template was evicted)
                            // - Cache overflow (exceeded MAX_CACHED_TEMPLATES limit)
                            error!(
                                template_id = %template_id,
                                block_hash = %block_hash,
                                cache_size = template_cache.lock().await.len(),
                                max_cache_size = MAX_CACHED_TEMPLATES,
                                "Block submission dropped - template not found in cache"
                            );
                        }
                    }
                }

                    _ = health_check_interval.tick() => {
                        let stats = shared_client.get_queue_stats();

                        if !shared_client.is_healthy() {
                            warn!(
                                pending = stats.pending_requests,
                                avg_time_ms = stats.avg_processing_time_ms,
                                critical_queue = stats.queue_sizes.critical,
                                "IPC queue unhealthy"
                            );
                        }
                    }

                    _ = detailed_stats_interval.tick() => {
                        let stats = shared_client.get_queue_stats();
                        debug!(
                            failed = stats.failed_requests,
                            avg_ms = stats.avg_processing_time_ms,
                            critical = stats.queue_sizes.critical,
                            high = stats.queue_sizes.high,
                            normal = stats.queue_sizes.normal,
                            low = stats.queue_sizes.low,
                            "IPC queue statistics"
                        );
                    }

                    // Health check
                   _ = tokio::time::sleep(tokio::time::Duration::from_secs(15)) => {
                        match shared_client.is_initial_block_download(Some(RequestPriority::Low)).await {
                            Ok(_) => {
                            }
                            Err(e) => {
                                error!(
                                    error = %e,
                                    socket = %ipc_socket_path,
                                    operation = "health_check",
                                    "Connection health check failed"
                                );
                                match classify_error(&e) {
                                    ErrorKind::ConnectionBroken => {
                                        error!(
                                            socket = %ipc_socket_path,
                                            operation = "health_check",
                                            "Dead connection detected - reconnecting"
                                        );
                                        break true;
                                    }
                                    ErrorKind::Temporary => {
                                        warn!(error = %e, "Non-critical health check error - will retry");
                                    }
                                    ErrorKind::LogicError => {
                                        warn!(error = %e, "Unexpected health check error - continuing");
                                        // Continue normal operation
                                    }
                                }
                            }
                        }
                    }
                }
            };

            if should_reconnect {
                warn!(retry_delay_secs = 5, "Connection lost - reconnecting");
                shared_client.shutdown().await.ok();
                tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
            }
        }
        // This line is never reached the function runs until process termination
        #[allow(unreachable_code)]
        Ok::<(), Box<dyn std::error::Error>>(())
    }).await
}

/// Retries block template requests with smart error handling and fallback strategies
///
/// This function implements a sophisticated retry mechanism that:
/// - Attempts template fetching up to `max_attempts` times
/// - Uses 500ms delays between attempts
/// - Accepts templates smaller than 512 bytes as fallback
/// - Returns immediately on connection errors for caller to handle reconnection
///
/// # Arguments
/// * `client` - The shared Bitcoin client for IPC communication
/// * `max_attempts` - Maximum retry attempts (typically 2-3 for fast response)
/// * `priority` - Request priority affecting queue position
/// * `context` - Context for logging
async fn get_template_with_retry(
    client: &mut SharedBitcoinClient,
    max_attempts: u32,
    priority: RequestPriority,
    context: &str,
    block_height: u32,
    initial_nonce: u32,
    network: Network,
) -> Result<client::BlockTemplate, Box<dyn std::error::Error>> {
    const MIN_TEMPLATE_SIZE: usize = 512;
    let config = CoinbaseConfig::for_network(network);
    let mut last_template: Option<client::BlockTemplate> = None;

    for attempt in 1..=max_attempts {
        match client
            .get_block_template_components(None, Some(priority))
            .await
        {
            Ok(components) => {
                match create_braidpool_template(
                    &components.components,
                    &config,
                    block_height,
                    initial_nonce,
                ) {
                    Ok(final_template) => {
                        let complete_block_bytes = final_template.complete_block_hex;
                        if complete_block_bytes.is_empty() {
                            return Err("Received empty template (0 bytes)".into());
                        }

                        let mut processed_template = (*components).clone();
                        processed_template.processed_block_hex = Some(complete_block_bytes);
                        last_template = Some(processed_template.clone());

                        if let Some(ref hex) = processed_template.processed_block_hex {
                            if hex.len() >= MIN_TEMPLATE_SIZE {
                                if attempt > 1 {
                                    info!(
                                        context = %context,
                                        size_bytes = %hex.len(),
                                        attempt = %attempt,
                                        "Got valid template on retry"
                                    );
                                }
                                return Ok(processed_template);
                            } else if attempt == max_attempts {
                                warn!(
                                    context = %context,
                                    size_bytes = %hex.len(),
                                    max_attempts = %max_attempts,
                                    "Template too small after max attempts - using anyway"
                                );
                                return Ok(processed_template);
                            } else {
                                warn!(
                                    context = %context,
                                    size_bytes = %hex.len(),
                                    attempt = %attempt,
                                    max_attempts = %max_attempts,
                                    "Template too small - retrying"
                                );
                            }
                        }
                    }
                    Err(e) => {
                        // Don't retry connection errors - let caller handle reconnection
                        let boxed_err: Box<dyn std::error::Error> = Box::new(e.clone());
                        if matches!(classify_error(&boxed_err), ErrorKind::ConnectionBroken) {
                            return Err(Box::new(e));
                        }

                        if attempt == max_attempts {
                            if let Some(template) = last_template {
                                warn!(
                                    context = %context,
                                    "Final attempt failed - using last template"
                                );
                                return Ok(template);
                            }
                            return Err(Box::new(e));
                        }

                        warn!(
                            context = %context,
                            attempt = %attempt,
                            error = %e,
                            "Template fetch attempt failed - retrying"
                        );
                    }
                }
            }
            Err(e) => {
                // Don't retry connection errors - let caller handle reconnection
                if matches!(classify_error(&e), ErrorKind::ConnectionBroken) {
                    return Err(e);
                }

                if attempt == max_attempts {
                    if let Some(template) = last_template {
                        warn!(context = %context, "Final attempt failed - using last template");
                        return Ok(template);
                    }
                    return Err(e);
                }

                warn!(
                    context = %context,
                    attempt = %attempt,
                    error = %e,
                    "Template fetch failed - retrying"
                );
            }
        }

        // Short delay between retries
        tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    }

    // This should never be reached due to the logic above, but just in case
    if let Some(template) = last_template {
        Ok(template)
    } else {
        Err("All attempts failed and no template available".into())
    }
}

fn create_braidpool_template(
    components: &BlockTemplateComponents,
    config: &CoinbaseConfig,
    block_height: u32,
    nonce: u32,
) -> Result<FinalTemplate, CoinbaseError> {
    let braidpool_commitment = b"braidpool_bead_metadata_hash_32b";
    //8 bytes that is extranonce has a size of 32 bits
    let extranonce = &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
    create_block_template(
        components,
        braidpool_commitment,
        extranonce,
        block_height,
        nonce,
        config,
    )
}
