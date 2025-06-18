//! Listens for block notifications and fetches new block templates via IPC
//! 
use tokio::sync::mpsc::Sender;
pub mod client;
pub use client::{SharedBitcoinClient, BitcoinNotification, RequestPriority, bytes_to_hex};

pub async fn ipc_block_listener(
    ipc_socket_path: String,
    block_template_tx: Sender<Vec<u8>>,
) -> Result<(), Box<dyn std::error::Error>> {
    log::info!("Starting IPC block listener on: {}", ipc_socket_path);
    
    let local = tokio::task::LocalSet::new();
    
    local.run_until(async move {
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
            let initial_sync_check = match shared_client.is_recently_synced(Some(RequestPriority::High)).await {
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
            const MIN_TEMPLATE_SIZE: usize = 100 * 1024;  // 100KB
            if initial_sync_check {
                match shared_client.get_block_template(None, Some(RequestPriority::High)).await {
                    Ok(initial_template) => {
                        let template_size = initial_template.len();                        
                        if template_size < MIN_TEMPLATE_SIZE {
                            log::warn!("Initial template size {} bytes is below {} KB - node may still be syncing mempool, waiting 15 seconds...", 
                                template_size, MIN_TEMPLATE_SIZE / 1024);
                            
                            // Wait and retry until we get a proper sized template
                            let mut retry_count = 0;
                            const MAX_RETRIES: u32 = 20;
                            loop {
                                tokio::time::sleep(tokio::time::Duration::from_secs(15)).await;
                                retry_count += 1;
                                
                                match shared_client.get_block_template(None, Some(RequestPriority::High)).await {
                                    Ok(retry_template) => {
                                        let retry_size = retry_template.len();
                                        
                                        if retry_size >= MIN_TEMPLATE_SIZE {
                                            log::info!("Got initial block template: {} bytes (retry {})", retry_size, retry_count);
                                            if let Err(e) = block_template_tx.send(retry_template).await {
                                                log::error!("Failed to send initial template: {}", e);
                                                continue; 
                                            }
                                            break; 
                                        } else if retry_count >= MAX_RETRIES {
                                            log::error!("Template size still {} bytes after {} retries - skipping initial template", 
                                                retry_size, MAX_RETRIES);
                                            break;
                                        } else {
                                            log::info!("Template size {} bytes still too small (retry {}/{}), waiting 15 more seconds...", 
                                                retry_size, retry_count, MAX_RETRIES);
                                        }
                                    }
                                    Err(e) => {
                                        log::error!("Failed to get template on retry {}: {}", retry_count, e);
                                        if is_connection_error(&e) {
                                            log::error!("Connection lost during template retry - restarting connection loop");
                                            continue; // Restart main connection loop
                                        }
                                        if retry_count >= MAX_RETRIES {
                                            log::error!("Template retries exhausted - skipping initial template");
                                            break;
                                        }
                                    }
                                }
                            }
                        } else {
                            log::info!("Got initial block template: {} bytes", template_size);
                            if let Err(e) = block_template_tx.send(initial_template).await {
                                log::error!("Failed to send initial template: {}", e);
                                continue; // Retry connection
                            }
                        }
                    }
                    Err(e) => {
                        log::error!("Failed to get initial template: {}", e);
                        if is_connection_error(&e) {
                            log::error!("Connection lost getting initial template - skipping initial template and will reconnect");
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
            let connection_lost = loop {
                tokio::select! {
                    notification = notification_receiver.recv() => {
                        match notification {
                            Some(BitcoinNotification::BlockConnected { height, hash, .. }) => {
                                let mut hash_reversed = hash.clone();
                                hash_reversed.reverse();
                                log::info!("New block #{} - Hash: {}", height, bytes_to_hex(&hash_reversed));
                                match shared_client.is_recently_synced(Some(RequestPriority::Critical)).await {
                                    Ok(true) => {
                                        match shared_client.get_block_template(None, Some(RequestPriority::Critical)).await {
                                            Ok(template_bytes) => {
                                                let template_size = template_bytes.len();
                                                const MIN_TEMPLATE_SIZE: usize = 100 * 1024; // 100KB
                                                
                                                if template_size < MIN_TEMPLATE_SIZE {
                                                    log::warn!("Template for block {} is {} bytes (< {} KB) - node may still be syncing, retrying...", 
                                                        height, template_size, MIN_TEMPLATE_SIZE / 1024);
                                                    
                                                    let mut retry_count = 0;
                                                    const MAX_RETRIES: u32 = 20;
                                                    let mut last_template = template_bytes;
                                                    let mut connection_lost_flag = false;
                                                    
                                                    while retry_count < MAX_RETRIES {
                                                        tokio::time::sleep(tokio::time::Duration::from_secs(15)).await;
                                                        retry_count += 1;
                                                        
                                                        match shared_client.get_block_template(None, Some(RequestPriority::Critical)).await {
                                                            Ok(retry_template) => {
                                                                let retry_size = retry_template.len();
                                                                last_template = retry_template;
                                                                
                                                                if retry_size >= MIN_TEMPLATE_SIZE {
                                                                    log::info!("Got block template: {} bytes for block {} (retry {})", retry_size, height, retry_count);
                                                                    if let Err(e) = block_template_tx.send(last_template.clone()).await {
                                                                        log::error!("Failed to send retry template: {}", e);
                                                                        connection_lost_flag = true;
                                                                        break;
                                                                    }
                                                                    break; 
                                                                } else {
                                                                    log::info!("Template size {} bytes (retry {}/{}), waiting 15 more seconds...", 
                                                                        retry_size, retry_count, MAX_RETRIES);
                                                                }
                                                            }
                                                            Err(e) => {
                                                                log::error!("Failed to get template on retry {} for block {}: {}", retry_count, height, e);
                                                                if is_connection_error(&e) {
                                                                    log::error!("Connection lost during template retry - reconnecting");
                                                                    connection_lost_flag = true;
                                                                    break;
                                                                }
                                                                log::warn!("Non-connection error on retry {}, continuing retries...", retry_count);
                                                            }
                                                        }
                                                    }
                                                    if connection_lost_flag {
                                                        break true; // Signal outer loop to reconnect
                                                    }

                                                    if retry_count >= MAX_RETRIES {
                                                        let final_size = last_template.len();
                                                        if final_size >= MIN_TEMPLATE_SIZE {
                                                            log::info!("Sending template after {} retries: {} bytes for block {}", 
                                                                MAX_RETRIES, final_size, height);
                                                        } else {
                                                            log::warn!("Exhausted {} retries for block {} - sending last template: {} bytes (< {} KB)", 
                                                                MAX_RETRIES, height, final_size, MIN_TEMPLATE_SIZE / 1024);
                                                        }
                                                        
                                                        if let Err(e) = block_template_tx.send(last_template).await {
                                                            log::error!("Failed to send last template after retries: {}", e);
                                                            break true;
                                                        }
                                                    }
                                                } else {
                                                    log::info!("Got block template: {} bytes for block {}", template_size, height);
                                                    if let Err(e) = block_template_tx.send(template_bytes).await {
                                                        log::error!("Failed to send template: {}", e);
                                                        break true;
                                                    }
                                                }
                                            }
                                            Err(e) => {
                                                log::error!("Failed to get template: {}", e);
                                                if is_connection_error(&e) {
                                                    log::error!("Connection lost getting template - restarting connection loop");
                                                    break true;
                                                }
                                            }
                                        }
                                    }
                                    Ok(false) => {
                                        log::warn!("Node not synced at block {} - skipping template request", height);
                                    }
                                    Err(e) => {
                                        log::error!("Sync check failed for block {}: {}", height, e);
                                        if is_connection_error(&e) {
                                            log::error!("Connection lost during sync check - will reconnect");
                                            break true;
                                        }
                                    }
                                }
                            }
                            
                            Some(BitcoinNotification::ConnectionLost { reason }) => {
                                log::error!("IPC connection lost: {}", reason);
                                break true;
                            }
                            
                            None => {
                                log::error!("Notification receiver closed - connection lost");
                                break true;
                            }
                            
                            _ => {
                                // Ignore other notifications
                            }
                        }
                    }
                    
                   _ = tokio::time::sleep(tokio::time::Duration::from_secs(15)) => {
                        match shared_client.is_initial_block_download(Some(RequestPriority::Low)).await {
                            Ok(_) => {
                                log::debug!("connection is still alive, continuing to listen for notifications");
                            }
                            Err(e) => {
                                log::error!("Connection health check failed: {}", e);
                                if is_connection_error(&e) {
                                    log::error!("Dead connection detected - reconnecting");
                                    break true;
                                }
                            }
                        }
                    }
                }
            };
            
            if connection_lost {
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
fn is_connection_error(error: &Box<dyn std::error::Error>) -> bool {
    let error_str = error.to_string().to_lowercase();
    
    error_str.contains("connection") && (
        error_str.contains("refused") ||
        error_str.contains("reset") ||
        error_str.contains("broken") ||
        error_str.contains("closed") ||
        error_str.contains("timeout") ||
        error_str.contains("no such file") ||
        error_str.contains("permission denied")
    ) || 
    error_str.contains("unix socket") || 
    error_str.contains("capnp") && error_str.contains("disconnected") ||
    error_str.contains("channel closed") ||
    error_str.contains("oneshot canceled") ||
    error_str.contains("receiver dropped") ||
    error_str.contains("mpsc") && error_str.contains("closed")
}