//! Listens for block notifications and fetches new block templates via IPC
use crate::config::CoinbaseConfig;
use crate::error::CoinbaseError;
use crate::error::{classify_error, ErrorKind};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::mpsc::Sender;
pub mod client;
use crate::template_creator::{create_block_template, FinalTemplate};
use bitcoin::Network;
pub use client::{
    bytes_to_hex, BitcoinNotification, BlockTemplateComponents, CheckBlockResult, RequestPriority,
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
    template_cache: Arc<tokio::sync::Mutex<HashMap<String, Arc<client::BlockTemplate>>>>,
    mut block_submission_rx: tokio::sync::mpsc::UnboundedReceiver<
        crate::stratum::BlockSubmissionRequest,
    >,
) -> Result<(), Box<dyn std::error::Error>> {
    log::info!(
        "Starting IPC block listener on: {} for network: {}",
        ipc_socket_path,
        network
    );
    let local = tokio::task::LocalSet::new();
    local.run_until(async move {
        loop {
            let mut health_check_interval = tokio::time::interval(tokio::time::Duration::from_secs(30));
            let mut detailed_stats_interval = tokio::time::interval(tokio::time::Duration::from_secs(100));
            let mut backoff_seconds = 1;
            let mut shared_client = match SharedBitcoinClient::new(&ipc_socket_path).await {
                Ok(client) => {
                    log::info!("IPC connection established");
                    client
                }
                Err(e) => {
                    log::error!("Failed to connect to IPC socket: {}", e);
                    log::info!("Retrying connection in 10 seconds...");
                    tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
                    continue;
                }
            };

            let initial_sync_result = loop {
                match shared_client.is_initial_block_download(Some(RequestPriority::High)).await {
                   Ok(in_ibd) => {
                        if in_ibd {
                            log::warn!("Node is in IBD (not synced) - proceeding anyway for now");
                            let result = Ok(false); // Not synced, but continue
                            break result;
                        } else {
                            log::info!("Node is synced and ready to be used");
                            break Ok(true);
                        }
                    }
                    Err(e) => {
                        log::error!("Initial sync check failed: {}", e);

                        match classify_error(&e) {
                            ErrorKind::Temporary => {
                                log::warn!("Temporary error during sync check, retrying in {} seconds...", backoff_seconds);
                                tokio::time::sleep(tokio::time::Duration::from_secs(backoff_seconds)).await;
                                backoff_seconds = std::cmp::min(backoff_seconds * 2, MAX_BACKOFF);
                                continue;
                            }
                            ErrorKind::ConnectionBroken => {
                                log::error!("Connection broken during initial sync check - reconnecting...");
                                break Err(ErrorKind::ConnectionBroken);
                            }
                            ErrorKind::LogicError => {
                                log::warn!("Unexpected error occurred during sync check, continuing without sync check");
                                break Ok(false);
                            }
                        }
                    }
                }
            };
            let tip_height = match shared_client.get_mining_tip_info(Some(RequestPriority::High)).await {
                    Ok((height, _hash)) => height,
                    Err(e) => {
                        log::error!("Failed to get mining tip info: {}", e);
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
                        log::info!("Got initial block template: {} bytes - Height: {}", template.components.block_hex.len(), tip_height);
                        if let Err(e) = block_template_tx.send(Arc::new(template)).await {
                            log::error!("Failed to send initial template: {}", e);
                            continue;
                        }
                    }
                    Err(e) => {
                        log::error!("Failed to get initial template: {}", e);
                        match classify_error(&e) {
                            ErrorKind::ConnectionBroken => {
                                log::error!("Connection lost getting initial template - reconnecting...");
                                continue; // Restart connection loop
                            }
                            ErrorKind::Temporary | ErrorKind::LogicError => {
                                log::warn!("Non-connection error occurred getting initial template, continuing anyway");
                                // Continue anyway - we'll get templates on block changes
                            }
                        }
                    }
                }
            }

            let mut notification_receiver = match shared_client.take_notification_receiver() {
                Some(receiver) => receiver,
                None => {
                    log::error!("Failed to get notification receiver - reconnecting");
                    tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
                    continue;
                }
            };

            log::info!("listening for block notifications...");

            // Listen for block connect notifications only
            let should_reconnect = loop {
                tokio::select! {
                    notification = notification_receiver.recv() => {
                        match notification {
                            Some(BitcoinNotification::TipChanged { height, hash, .. }) => {
                                let mut hash_reversed = hash.clone();
                                hash_reversed.reverse();
                                log::info!("New block #{} - Hash: {}", height, bytes_to_hex(&hash_reversed));
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
                                                    log::info!(
                                                        "Got block template data: {} bytes",
                                                        template.processed_block_hex.as_ref().map(|v| v.len()).unwrap_or(0)
                                                    );
                                                    if let Err(e) = block_template_tx.send(Arc::new(template)).await {
                                                        log::error!("Failed to send template: {}", e);
                                                        break true;
                                                    }
                                                }
                                                Err(e) => {
                                                    log::error!("Failed to get block template: {}", e);
                                                    match classify_error(&e) {
                                                        ErrorKind::ConnectionBroken => {
                                                            log::error!("Connection lost, restarting connection loop");
                                                            break true;
                                                        }
                                                        ErrorKind::Temporary => {
                                                            log::warn!("Non critical error occurred getting template for block {}, will retry on next block", height);
                                                        }
                                                        ErrorKind::LogicError => {
                                                            log::warn!("Unexpected error occurred getting template for block {}, continuing", height);
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            log::warn!("Node was in IBD at block {}, skipping template request", height);
                                        }
                                    }
                                    Err(e) => {
                                        log::error!("Sync check failed for block {}: {}", height, e);
                                        match classify_error(&e) {
                                            ErrorKind::ConnectionBroken => {
                                                log::error!("Connection lost during sync check, reconnecting...");
                                                break true;
                                            }
                                            ErrorKind::Temporary => {
                                                log::warn!("Non critical error occurred during sync check for block {}, will retry on next block", height);
                                            }
                                            ErrorKind::LogicError => {
                                                log::warn!("Unexpected error occurred during sync check for block {}, continuing", height);
                                            }
                                        }
                                    }
                                }
                            }

                            Some(BitcoinNotification::ConnectionLost { reason }) => {
                                log::error!("Connection lost: {}", reason);
                                break true;
                            }

                            None => {
                                log::error!("Failed to receive notifications. Maybe the connection was lost");
                                break true;
                            }
                        }
                    }

                    submission = block_submission_rx.recv() => {
                    if let Some(submission) = submission {
                        let template_opt = template_cache.lock().await.get(&submission.template_id).cloned();

                        if let Some(ipc_template) = template_opt {
                            match shared_client
                                .submit_solution(
                                    ipc_template,
                                    submission.version as u32,
                                    submission.timestamp,
                                    submission.nonce,
                                    bitcoin::consensus::encode::serialize(&submission.coinbase_transaction),
                                    Some(RequestPriority::Critical),
                                )
                                .await
                            {
                                Ok(result) => {
                                    if result.success {
                                        log::info!("Block {} ACCEPTED by Bitcoin Core!", submission.template_id);
                                    } else {
                                        log::error!("Block {} REJECTED: {}", submission.template_id, result.reason);
                                    }
                                }
                                Err(e) => {
                                    log::error!("Error submitting block {}: {}", submission.template_id, e);
                                }
                            }
                        } else {
                            log::error!(
                                "BLOCK SUBMISSION DROPPED\n\
                                Template ID: {} NOT FOUND IN CACHE\n\
                                This represents a potentially valid Bitcoin block that cannot be submitted!\n\
                                Possible causes:\n\
                                - Template expired (current size: {}, Max size: {} templates)\n\
                                - Cache overflow (old template was evicted)",
                                submission.template_id,
                                template_cache.lock().await.len(),
                                90,
                           );
                        }
                    }
                }

                    _ = health_check_interval.tick() => {
                        let stats = shared_client.get_queue_stats();

                        if !shared_client.is_healthy() {
                            log::warn!("IPC queue unhealthy - Pending: {}, Avg time: {}ms, Critical queue: {}",
                              stats.pending_requests,
                                stats.avg_processing_time_ms,
                                stats.queue_sizes.critical);
                        }
                    }

                    _ = detailed_stats_interval.tick() => {
                        let stats = shared_client.get_queue_stats();
                        log::info!("IPC Stats - Failed: {}, Avg: {}ms, Queues: C:{} H:{} N:{} L:{}",
                            stats.failed_requests,
                            stats.avg_processing_time_ms,
                            stats.queue_sizes.critical,
                            stats.queue_sizes.high,
                            stats.queue_sizes.normal,
                            stats.queue_sizes.low);
                    }

                    // Health check
                   _ = tokio::time::sleep(tokio::time::Duration::from_secs(15)) => {
                        match shared_client.is_initial_block_download(Some(RequestPriority::Low)).await {
                            Ok(_) => {
                            }
                            Err(e) => {
                                log::error!("Connection health check failed: {}", e);
                                match classify_error(&e) {
                                    ErrorKind::ConnectionBroken => {
                                        log::error!("Dead connection detected, reconnecting...");
                                        break true;
                                    }
                                    ErrorKind::Temporary => {
                                        log::warn!("Non critical error occurred in health check, will retry on next interval");
                                    }
                                    ErrorKind::LogicError => {
                                        log::warn!("Unexpected error occurred in health check, continuing operation");
                                        // Continue normal operation
                                    }
                                }
                            }
                        }
                    }
                }
            };

            if should_reconnect {
                log::warn!("Connection lost, attempting to reconnect in 5 seconds...");
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
                                    log::info!(
                                        "{}: Got valid template {} bytes (attempt {})",
                                        context,
                                        hex.len(),
                                        attempt
                                    );
                                }
                                return Ok(processed_template);
                            } else if attempt == max_attempts {
                                log::warn!(
                                    "{}: Template too small ({} bytes) after {} attempts, using anyway",
                                    context,
                                    hex.len(),
                                    max_attempts
                                );
                                return Ok(processed_template);
                            } else {
                                log::warn!(
                                    "{}: Template too small ({} bytes), retrying... (attempt {}/{})",
                                    context,
                                    hex.len(),
                                    attempt,
                                    max_attempts
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
                                log::warn!(
                                    "{}: Final attempt failed, using last template",
                                    context
                                );
                                return Ok(template);
                            }
                            return Err(Box::new(e));
                        }

                        log::warn!(
                            "{}: Attempt {} failed: {}, retrying...",
                            context,
                            attempt,
                            e
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
                        log::warn!("{}: Final attempt failed, using last template", context);
                        return Ok(template);
                    }
                    return Err(e);
                }

                log::warn!(
                    "{}: Attempt {} failed: {}, retrying...",
                    context,
                    attempt,
                    e
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
