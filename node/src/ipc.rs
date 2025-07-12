//! Listens for block notifications and fetches new block templates via IPC
use tokio::sync::mpsc::Sender;
use tokio::sync::oneshot;
pub mod client;
pub use client::{bytes_to_hex, BitcoinNotification, RequestPriority, SharedBitcoinClient};

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
    block_template_tx: Sender<Vec<u8>>,
) -> Result<(), Box<dyn std::error::Error>> {
    log::info!("Starting IPC block listener on: {}", ipc_socket_path);
    let local = tokio::task::LocalSet::new();
    local.run_until(async move {
        let mut health_check_interval = tokio::time::interval(tokio::time::Duration::from_secs(30));
        let mut detailed_stats_interval = tokio::time::interval(
            tokio::time::Duration::from_secs(100)
        );
        loop {
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

            let initial_sync_check = match
                shared_client.is_recently_synced(Some(RequestPriority::High)).await
            {
                Ok(is_synced) => {
                    if !is_synced {
                        log::warn!("Node is not synced - waiting for sync to complete");
                    } else {
                        log::info!("Node is synced and ready to be used");
                    }
                    is_synced
                }
                Err(e) => {
                    log::error!("Initial sync check failed: {}", e);
                    if is_connection_error(&e) {
                        log::error!("Connection lost during initial sync check - reconnecting");
                        continue; // Restart the main connection loop
                    }
                    log::warn!("Continuing without sync check");
                    false
                }
            };

            // Only try to get initial template if node is synced
            if initial_sync_check {
                match get_template_with_retry(
                    &mut shared_client,
                    3,
                    RequestPriority::High,
                    "initial template"
                ).await {
                    Ok(template) => {
                        log::info!("Got initial block template: {} bytes", template.len());
                        if let Err(e) = block_template_tx.send(template).await {
                            log::error!("Failed to send initial template: {}", e);
                            continue;
                        }
                    }
                    Err(e) => {
                        log::error!("Failed to get initial template: {}", e);
                        if is_connection_error(&e) {
                            log::error!("Connection lost getting initial template - reconnecting");
                            continue;
                        }
                        // Continue anyway - we'll get templates on block changes
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
                            Some(BitcoinNotification::BlockConnected { height, hash, .. }) => {
                                let mut hash_reversed = hash.clone();
                                hash_reversed.reverse();
                                log::info!("New block #{} - Hash: {}", height, bytes_to_hex(&hash_reversed));
                                match shared_client.is_recently_synced(Some(RequestPriority::Critical)).await {
                                    Ok(true) => {
                                        match get_template_with_retry(
                                            &mut shared_client,
                                            2,
                                            RequestPriority::Critical,
                                            &format!("block {}", height)
                                        ).await {
                                            Ok(template) => {
                                                log::info!("Got block template data: {} bytes", template.len());
                                                if let Err(e) = block_template_tx.send(template).await {
                                                    log::error!("Failed to send template: {}", e);
                                                    break true;
                                                }
                                            }
                                            Err(e) => {
                                                log::error!("Failed to get block template: {}", e);
                                                if is_connection_error(&e) {
                                                    log::error!("Connection lost, restarting connection loop");
                                                    break true;
                                                }
                                            }
                                        }
                                    }
                                    Ok(false) => {
                                        log::warn!("Node was not synced at block {}, skipping template request", height);
                                    }
                                    Err(e) => {
                                        log::error!("Sync check failed for block {}: {}", height, e);
                                        if is_connection_error(&e) {
                                            log::error!("Connection lost during sync check, reconnecting...");
                                            break true;
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

                            _ => {
                                // Ignore other notifications
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
                                if is_connection_error(&e) {
                                    log::error!("Dead connection detected, reconnecting...");
                                    break true;
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
            } else {
                break;
            }
        }

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
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    const MIN_TEMPLATE_SIZE: usize = 512;
    let mut last_template = Vec::new();

    for attempt in 1..=max_attempts {
        match client.get_block_template(None, Some(priority)).await {
            Ok(template) => {
                last_template = template;
                if last_template.len() >= MIN_TEMPLATE_SIZE {
                    if attempt > 1 {
                        log::info!(
                            "{}: Got valid template {} bytes (attempt {})",
                            context,
                            last_template.len(),
                            attempt
                        );
                    }
                    return Ok(last_template);
                } else if attempt == max_attempts {
                    log::warn!(
                        "{}: Template too small ({} bytes) after {} attempts, using anyway",
                        context,
                        last_template.len(),
                        max_attempts
                    );
                    return Ok(last_template);
                } else {
                    log::warn!(
                        "{}: Template too small ({} bytes), retrying... (attempt {}/{})",
                        context,
                        last_template.len(),
                        attempt,
                        max_attempts
                    );
                }
            }
            Err(e) => {
                // Don't retry connection errors - let caller handle reconnection
                if is_connection_error(&e) {
                    return Err(e);
                }

                if attempt == max_attempts {
                    // If we have a previous template, use it
                    if !last_template.is_empty() {
                        log::warn!(
                            "{}: Final attempt failed, using last template: {} bytes",
                            context,
                            last_template.len()
                        );
                        return Ok(last_template);
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
    if !last_template.is_empty() {
        Ok(last_template)
    } else {
        Err("All attempts failed and no template available".into())
    }
}

/// Determines if an error indicates a connection/communication failure
///
/// This function classifies errors to distinguish between:
/// * Connection errors: Require reconnection, no point in retrying
/// * Logic errors: May succeed on retry (temporary issues)
fn is_connection_error(error: &Box<dyn std::error::Error>) -> bool {
    if error.downcast_ref::<std::io::Error>().is_some()
        || error.downcast_ref::<oneshot::error::RecvError>().is_some()
    {
        return true;
    }
    let error_str = error.to_string().to_lowercase();
    let connection_keywords = [
        "connection refused",
        "connection reset",
        "connection lost",
        "broken pipe",
        "no such file",
        "permission denied",
        "disconnected",
        "channel closed",
        "oneshot canceled",
        "receiver dropped",
        "invalid thread handle",
        "null capability pointer",
        "method not implemented",
        "remote exception",
        "capability disconnected",
        "bootstrap failed",
    ];

    connection_keywords
        .iter()
        .any(|keyword| error_str.contains(keyword))
}
