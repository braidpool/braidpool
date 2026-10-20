use bitcoin::hashes::Hash;
use clap::Parser;
use futures::lock::Mutex;
use libp2p::{floodsub, identity::Keypair};
use node::audit;
use node::db::db_handlers::fetch_beads_in_batch;
use node::db::db_handlers::FETCH_BEAD_BATCH_SIZE;
use node::upstream_pool;
use node::utils::compute_block_hash;
use node::utils::resolve_datadir;
use node::SwarmHandler;
use node::{
    behaviour::BRAIDPOOL_TOPIC,
    braid, cli, config,
    db::db_handlers::DBHandler,
    ibd_manager::{IBDManager, IBD_TRIGGER_AFTER},
    ipc_template_consumer,
    peer_manager::PeerManager,
    rpc_server::{run_rpc_server, BitcoinRpcConfig, RpcProxyCommand},
    setup_tracing,
    stratum::{
        BlockTemplate, ConnectionMapping, GlobalJobStore, Notifier, NotifyCmd, Server,
        StratumServerConfig,
    },
    swarm::{
        bootstrap::{dial_additional_nodes, setup_and_bootstrap},
        builder::{build_swarm, parse_bind_address, SwarmConfig},
        config::DEFAULT_P2P_PORT,
        p2p_event_loop, SwarmContext,
    },
    SwarmCommand, TemplateId,
};
use std::collections::HashMap;
use std::error::Error;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::{fs, time::Duration};
use tokio::sync::{
    mpsc::{self},
    RwLock,
};
use tokio_util::sync::CancellationToken;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // Initialize tracing with colors and module prefixes
    setup_tracing()?;
    // Parse CLI arguments
    let args = cli::Cli::parse();
    let network = match config::parse_network_name(&args.network) {
        Ok(network) => network,
        Err(error) => {
            error!(
                network = %args.network,
                valid_networks = %config::SUPPORTED_NETWORKS.join(", "),
                "Invalid network specified"
            );
            return Err(Box::<dyn Error>::from(error));
        }
    };
    info!(network = %network, is_cpunet = network.is_cpunet(), "Network selected");
    // Audit mode requires mainnet for the verification to be passed so early error
    // will allow user to verify that .
    if args.audit && network != config::PoolNetwork::Bitcoin(bitcoin::Network::Bitcoin) {
        error!(
            network = %network,
            "Audit mode requires --network mainnet"
        );
        return Err(Box::<dyn Error>::from(
            "audit mode requires --network mainnet",
        ));
    }
    let (mut ibd_manager, ibd_command_tx) = IBDManager::new();
    //IBD cache handler
    let _ibd_handler = tokio::spawn(async move {
        ibd_manager.run_ibd_handler().await;
    });
    //False if not under ibd or in audit mode otherwise true at start will be in IBD by default
    let ibd_or_not: AtomicBool = if args.audit {
        AtomicBool::new(false)
    } else {
        AtomicBool::new(true)
    };
    let ibd_spinlock = Arc::new(ibd_or_not);

    // Resolving datadir or the default datadir if not provided .
    let datadir_path = resolve_datadir(&args.datadir)?;
    // Initializing the braid object with read write lock
    //for supporting concurrent readers and single writer
    let braid: Arc<RwLock<braid::Braid>> =
        Arc::new(RwLock::new(braid::Braid::new(Vec::from([]), network)));
    let mut optional_db_pool = None;
    let db_tx;

    if !args.audit {
        //Initializing DB and db command handler
        let (mut db_handler, tx) = DBHandler::new(&datadir_path, network).await.map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("Database initialization failed: {:?}", e),
            )
        })?;
        db_tx = tx;
        optional_db_pool = Some(db_handler.db_connection_pool.clone());
        //Reconstructing local braid upon startup
        let db_connection_pool_ref = db_handler.db_connection_pool.clone();

        //Starting the `query_handler` task
        tokio::spawn(async move {
            let _res = db_handler.insert_query_handler().await;
        });

        let braid_ref = braid.clone();
        // FIXME instead we should look 144 blocks back from the bitcoin tip (1 day) and load beads
        // starting from that block as genesis
        let network_ref = network;
        let initial_bead_fetch_handle = tokio::spawn(async move {
            let mut guard = braid_ref.write().await;
            let fetched_beads =
                fetch_beads_in_batch(&db_connection_pool_ref, FETCH_BEAD_BATCH_SIZE).await?;
            info!(beads = fetched_beads.len(), "Beads loaded from DB");
            for bead in &fetched_beads {
                let curr_bead_status = guard.extend(&bead);
                debug!(
                    hash = ?compute_block_hash(&bead.block_header,network_ref),
                    status = ?curr_bead_status,
                    "Bead inserted"
                );
            }
            Ok::<(), node::error::DBErrors>(())
        });

        match initial_bead_fetch_handle.await {
            Ok(Ok(())) => info!("Initial bead fetch completed successfully"),
            Ok(Err(e)) => {
                error!(error = ?e, "Failed to fetch beads from DB during startup");
                return Err(format!("Database bead fetch failed: {:?}", e).into());
            }
            Err(e) => {
                return Err(format!("Initial bead fetch task failed: {}", e).into());
            }
        }
    } else {
        // Create a dummy channel for SwarmHandler so it doesn't crash when it tries to broadcast in audit mode
        let (tx, mut rx) = mpsc::channel(1);
        db_tx = tx;

        // Keep the receiver alive in a background sink so channel sends don't fail
        tokio::spawn(async move {
            while let Some(msg) = rx.recv().await {
                trace!(message = ?msg, "Audit dummy sink; Dropping standard DB message");
            }
        });
    }
    let latest_template_id = Arc::new(Mutex::new(TemplateId::default()));
    let latest_template_id_for_notifier = latest_template_id.clone();
    let latest_template_id_for_consumer = latest_template_id.clone();
    // Initializing the peer manager (shared between swarm and RPC server)
    // Using RwLock to allow concurrent reads (RPC server) while swarm handler can write
    let peer_manager_arc = Arc::new(tokio::sync::RwLock::new(PeerManager::new(8)));

    //One will go into the IPC and the other will go to the `notifier`
    let (notification_tx, notification_rx) = mpsc::channel::<NotifyCmd>(1024);
    //latest available template to be cached for the newest connection until new job is received
    let latest_template = Arc::new(Mutex::new(BlockTemplate::default()));

    //latest available template merkle branch
    let latest_template_merkle_branch = Arc::new(Mutex::new(Vec::new()));
    let mut latest_template_ref = latest_template.clone();
    let mut latest_template_merkle_branch_ref = latest_template_merkle_branch.clone();
    let ipc_socket_path_for_blocking = args.ipc_socket.clone();

    let notification_tx_for_ipc = notification_tx.clone();
    let latest_template_for_ipc = latest_template.clone();
    let latest_template_merkle_branch_for_ipc = latest_template_merkle_branch.clone();
    let network_for_ipc = network;

    //Connection mapping for all the downstream connection connected to the stratum server
    let connection_mapping = Arc::new(tokio::sync::RwLock::new(ConnectionMapping::new()));
    // Clone connection_mapping for RPC server before it's used in async move blocks
    let connection_mapping_for_rpc = Arc::clone(&connection_mapping);
    // Create RPC proxy command channel - sender goes to RPC server, receiver goes to IPC handler
    let (rpc_proxy_tx, rpc_proxy_rx) = tokio::sync::mpsc::unbounded_channel::<RpcProxyCommand>();
    // peer_manager_arc is created above and shared between swarm and RPC server
    //spawning the rpc server
    let rpc_addr = args.rpc_bind.to_string();
    let bitcoin_rpc_config = BitcoinRpcConfig::from_cli_args(&args).unwrap_or_else(|e| {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    });

    let rpc_braid = Arc::clone(&braid);
    let rpc_peer_manager = peer_manager_arc.clone();
    let rpc_connection_mapping = connection_mapping_for_rpc.clone();
    let rpc_latest_template = latest_template.clone();
    let rpc_db_tx = db_tx.clone();
    let server_join = tokio::spawn(async move {
        run_rpc_server(
            rpc_braid,
            &rpc_addr,
            rpc_peer_manager,
            rpc_connection_mapping,
            rpc_latest_template,
            rpc_proxy_tx,
            bitcoin_rpc_config,
            rpc_db_tx,
        )
        .await
    });
    let (_rpc_addr, dashboard_notifier) = match server_join.await {
        Ok(Ok(tuple)) => tuple,
        Ok(Err(())) => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "RPC server startup failed",
            )
            .into());
        }
        Err(e) => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("RPC server task failed: {}", e),
            )
            .into());
        }
    };
    //Communication bridge between stratum and network swarm and swarm commands also, for communicating share population and propogating them further
    let (swarm_handler, swarm_command_receiver) = SwarmHandler::new(
        Arc::clone(&braid),
        db_tx.clone(),
        Arc::clone(&dashboard_notifier),
    );

    //Swarm command sender
    let swarm_command_sender = swarm_handler.command_sender.clone();
    let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
    //cloning the channel to be sent across different interfaces
    let notification_tx_clone = notification_tx.clone();
    //Connection mapping for all the downstream connection connected to the stratum server
    let connection_mapping_for_shutdown = connection_mapping.clone();
    //Global job store shared across all connected miners
    let global_job_store = Arc::new(Mutex::new(GlobalJobStore::new(
        node::GLOBAL_JOB_STORE_CAPACITY,
    )));
    //Intializing `notifier` for mining.notify
    let mut notifier: Notifier = Notifier::new(notification_rx, Arc::clone(&global_job_store));
    //Stratum configuration initialization
    let stratum_config = StratumServerConfig::default();
    let stratum_bind_address = format!("{}:{}", stratum_config.hostname, args.stratum_port);
    let stratum_listener = tokio::net::TcpListener::bind(&stratum_bind_address).await?;
    let stratum_config = StratumServerConfig {
        audit_mode: args.audit,
        audit_miner_difficulty: args.miner_difficulty,
        ..Default::default()
    };
    let (block_submission_tx, block_submission_rx) =
        tokio::sync::mpsc::unbounded_channel::<node::stratum::BlockSubmissionRequest>();
    //IBD notifier task after peer_discovery
    let swarm_command_sender_ref = swarm_command_sender.clone();
    if !args.audit {
        let _ibd_trigger_handler = tokio::spawn(async move {
            tokio::time::sleep(Duration::from_secs(IBD_TRIGGER_AFTER)).await;
            //Sending IBD initiating command
            match swarm_command_sender_ref
                .send(SwarmCommand::InitiateIBD)
                .await
            {
                Ok(_) => {
                    info!("IBD trigger sent");
                }
                Err(error) => {
                    error!(error=?error,"An error occurred while initiating IBD after waiting for peer discovery - ");
                }
            };
        });
    } else {
        info!("Skipping IBD invoking, currently in audit mode.")
    }
    //Initializing stratum server
    let mut stratum_server = Server::new(
        stratum_config,
        connection_mapping.clone(),
        Some(block_submission_tx),
        network,
    );

    let (main_shutdown_tx, _main_shutdown_rx) =
        mpsc::channel::<tokio::signal::unix::SignalKind>(32);
    let main_task_token = CancellationToken::new();
    let ipc_task_token = main_task_token.clone();
    let mut upstream_cache_for_notifier = None;
    let (upstream_ready_tx, upstream_ready_rx) = tokio::sync::oneshot::channel::<()>();
    let (
        upstream_share_tx_option,
        upstream_configure_tx_option,
        audit_dag_option,
        audit_dag_for_notifier,
    ) = if args.audit {
        // Validate CLI arguments for audit mode
        if args.upstream_host.is_none() {
            error!("--upstream-host is required when --audit is enabled");
            std::process::exit(1);
        }
        if args.upstream_username.is_none() {
            error!("--upstream-username is required when --audit is enabled");
            std::process::exit(1);
        }
        info!("Audit mode is enabled acting as a proxy to the upstream pool");
        info!(
            "Upstream: {}:{}",
            args.upstream_host.as_ref().unwrap(),
            args.upstream_port
        );

        // Initialize audit records
        let audit_dag = match audit::AuditDAG::new_with_db(Arc::clone(&braid), &datadir_path).await
        {
            Ok(dag) => Arc::new(Mutex::new(dag)),
            Err(e) => {
                error!("Failed to initialize audit DAG with database: {}", e);
                std::process::exit(1);
            }
        };

        match audit_dag.lock().await.load_from_db().await {
            Ok(Some(latest_composite_hash)) => {
                let commitment_bytes = latest_composite_hash.to_byte_array()
                    [..crate::audit::COMMITMENT_BYTES]
                    .to_vec();
                let mut conn_map = connection_mapping.write().await;
                conn_map.current_bead_commitment = commitment_bytes.clone();
                drop(conn_map);

                info!(
                    commitment = %hex::encode(&commitment_bytes),
                    composite_hash = %latest_composite_hash,
                    "Restored global bead commitment from database"
                );
            }
            Ok(None) => {
                info!("No previous beads in database, starting from genesis commitment");
            }
            Err(e) => {
                warn!("Failed to load bead from database: {}", e);
            }
        }

        let audit_dag_for_notifier_inner: Option<Arc<Mutex<audit::AuditDAG>>> =
            Some(audit_dag.clone());
        let audit_dag_for_stratum = audit_dag.clone();
        let audit_dag_for_audit_log = audit_dag.clone();
        // Setting upstream pool configuration from CLI args
        let upstream_config = upstream_pool::UpstreamPoolConfig {
            hostname: args.upstream_host.clone().unwrap(),
            port: args.upstream_port,
            username: args.upstream_username.clone().unwrap(),
            password: args.upstream_password.clone(),
        };
        // Initialize upstream cache
        let upstream_cache = upstream_pool::UpstreamCache::new();
        let upstream_cache_clone = upstream_cache.clone();
        upstream_cache_for_notifier = Some(upstream_cache.clone());
        let global_job_store_for_upstream_cleanup = global_job_store.clone();
        // For forwarding shares to upstream pool (stratum server -> upstream client), using Arc<Mutex<Receiver>> so the receiver survives reconnections,
        // Buffer 50,000 shares to survive upstream lag spikes without blocking miners
        let (upstream_share_tx, upstream_share_rx) =
            mpsc::channel::<upstream_pool::UpstreamShare>(50000);
        let upstream_share_rx = Arc::new(tokio::sync::Mutex::new(upstream_share_rx));
        // For receiving jobs from upstream pool (upstream client -> notifier)
        let (upstream_job_tx, upstream_job_rx) =
            mpsc::channel::<node::stratum::JobNotification>(1024);
        let upstream_job_rx = Arc::new(tokio::sync::Mutex::new(upstream_job_rx));
        // For receiving responses from upstream (upstream client -> stratum server)
        let (upstream_response_tx, upstream_response_rx) =
            mpsc::channel::<(String, serde_json::Value, u64)>(1024);
        let upstream_response_rx = Arc::new(tokio::sync::Mutex::new(upstream_response_rx));
        let (audit_log_tx, mut audit_log_rx) =
            tokio::sync::mpsc::channel::<(crate::audit::ShareId, serde_json::Value)>(2048);
        // For forwarding configure requests to upstream pool
        let (configure_tx, configure_rx) =
            mpsc::channel::<(serde_json::Value, u64, mpsc::Sender<serde_json::Value>)>(50000);
        let configure_rx = Arc::new(tokio::sync::Mutex::new(configure_rx));
        // cancellation tokens
        let upstream_response_task_token = main_task_token.clone();
        let upstream_job_task_token = main_task_token.clone();

        let connection_mapping_for_responses = connection_mapping.clone();
        let upstream_response_rx_clone = upstream_response_rx.clone();
        tokio::spawn(async move {
            info!(component = "audit", "Starting audit log listener");
            let mut total_shares = 0u64;
            let mut accepted_shares = 0u64;
            let mut rejected_shares = 0u64;

            while let Some((share_id, response)) = audit_log_rx.recv().await {
                total_shares += 1;
                let error = response.get("error").filter(|v| !v.is_null());
                let result_is_success = match response.get("result") {
                    Some(val) if val.is_boolean() => val.as_bool().unwrap_or(false),
                    Some(val) if val.is_null() => true,
                    None => error.is_none(),
                    _ => false,
                };

                let mut dag = audit_dag_for_audit_log.lock().await;
                dag.update_upstream_response(&share_id, result_is_success);
                debug!(
                    share_id = %share_id,
                    accepted = %result_is_success,
                    "Updated audit record with upstream response"
                );
                drop(dag);

                if let Some(err) = error {
                    rejected_shares += 1;
                    warn!(
                        component = "audit",
                        total = total_shares,
                        accepted = accepted_shares,
                        rejected = rejected_shares,
                        acceptance_rate = format!(
                            "{:.2}%",
                            (accepted_shares as f64 / total_shares as f64) * 100.0
                        ),
                        "Upstream REJECTED share: {:?}",
                        err
                    );
                } else if result_is_success {
                    accepted_shares += 1;
                    debug!(
                        component = "audit",
                        total = total_shares,
                        acceptance_rate = format!(
                            "{:.2}%",
                            (accepted_shares as f64 / total_shares as f64) * 100.0
                        ),
                        "Upstream confirmed share"
                    );
                } else {
                    rejected_shares += 1;
                    warn!(component = "audit", "Upstream returned invalid result");
                }
                if total_shares % 10 == 0 {
                    info!(
                        component = "audit",
                        total = total_shares,
                        accepted = accepted_shares,
                        rejected = rejected_shares,
                        acceptance_rate = format!(
                            "{:.2}%",
                            (accepted_shares as f64 / total_shares as f64) * 100.0
                        ),
                        "Audit statistics"
                    );
                }
            }
        });

        tokio::spawn(async move {
            info!("Starting upstream response handler");
            loop {
                tokio::select! {
                            received = async {
                                let mut rx = upstream_response_rx_clone.lock().await;
                                rx.recv().await
                        } => {
                        match received {
                            Some((worker_name, response, original_request_id)) => {
                                debug!("Upstream response for {}: {:?}", worker_name, response);
                                let conn_map = connection_mapping_for_responses.read().await;
                                if let Some(channel) = conn_map.get_channel_for_worker(&worker_name) {
                                    let miner_response = serde_json::json!({
                                        "id": original_request_id,
                                        "result": response.get("result").unwrap_or(&serde_json::json!(null)),
                                        "error": response.get("error").unwrap_or(&serde_json::json!(null))
                                    });

                                    if let Err(e) = channel
                                        .send(serde_json::to_string(&miner_response).unwrap())
                                        .await
                                    {
                                        error!(
                                            "Failed to forward response to worker {}: {}",
                                            worker_name, e
                                        );
                                    } else {
                                        trace!(
                                            "Forwarded upstream response to worker {} (id={})",
                                            worker_name, original_request_id
                                        );
                                    }
                                } else {
                                    warn!("Worker '{}' not found in connection mapping", worker_name);
                                }
                            }
                            None => {
                                // Channel closed, this means all senders were dropped
                                // In our design, this shouldn't happen because we clone senders
                                // But if it does, log and wait before checking again
                                if upstream_response_task_token.is_cancelled() {
                                    break;
                                }
                                warn!("Upstream response channel returned None - waiting for reconnection");
                                tokio::time::sleep(Duration::from_secs(1)).await;
                            }
                        }
                    }
                    _ = upstream_response_task_token.cancelled() => {
                        info!("Upstream response handler shutting down");
                        break;
                    }
                }
            }
        });

        // Forwards jobs from upstream to the notifier
        let notification_tx_for_upstream_jobs = notification_tx.clone();
        let upstream_job_rx_clone = upstream_job_rx.clone();
        tokio::spawn(async move {
            info!("Starting persistent upstream job handler");
            loop {
                tokio::select! {
                        received = async {
                        let mut rx = upstream_job_rx_clone.lock().await;
                        rx.recv().await
                    } => {
                    match received {
                        Some(job) => {
                            info!("Received job from upstream pool: {}", job.job_id);

                            // Marking each job as clean_jobs=true to make the DAG consistent and consensus correct, without
                            // that a miner can produce shares which use the previous commitment on lower difficulties
                            // or in general.
                            let mut job = job;
                            job.clean_jobs = true;

                            if let Err(e) = notification_tx_for_upstream_jobs
                                .send(NotifyCmd::SendUpstreamJob {
                                    job_notification: job,
                                })
                                .await
                            {
                                error!("Failed to forward upstream job: {}", e);
                            } else {
                                debug!("Forwarded upstream job to notifier");
                            }
                        }
                        None => {
                            warn!("Upstream job channel returned None, waiting for reconnection...");
                            tokio::time::sleep(Duration::from_secs(1)).await;
                        }
                    }
                }
                _ = upstream_job_task_token.cancelled() => {
                            info!("Upstream job handler shutting down");
                            break;
                    }
                }
            }
        });

        let notification_tx_for_upstream_difficulty = notification_tx.clone();
        let connection_mapping_for_upstream = connection_mapping.clone();
        let upstream_task_token = main_task_token.clone();
        let mut upstream_ready_tx_option = Some(upstream_ready_tx);
        tokio::spawn(async move {
            // Reconnection state
            let mut retry_count: u32 = 0;
            let base_delay = Duration::from_secs(5);
            let max_delay = Duration::from_secs(60);
            let mut last_successful_connection = std::time::Instant::now();

            loop {
                if upstream_task_token.is_cancelled() {
                    info!("Upstream pool task received shutdown signal");
                    break;
                }
                info!(
                    "Starting upstream pool connection attempt #{} to {}:{}",
                    retry_count + 1,
                    upstream_config.hostname,
                    upstream_config.port
                );

                // These are recreated for each connection attempt
                let (upstream_extranonce_tx, mut upstream_extranonce_rx) =
                    mpsc::channel::<(String, usize)>(1);
                let (upstream_difficulty_tx, mut upstream_difficulty_rx) = mpsc::channel::<f64>(1);
                let first_connection_ready_tx = upstream_ready_tx_option.take();
                let connection_mapping_for_extranonce = connection_mapping_for_upstream.clone();
                let extranonce_task = tokio::spawn(async move {
                    let mut ready_tx = first_connection_ready_tx;

                    while let Some((extranonce1, extranonce2_size)) =
                        upstream_extranonce_rx.recv().await
                    {
                        info!(
                            "Received upstream extranonce: {}, size: {}",
                            extranonce1, extranonce2_size
                        );
                        let mut conn_map = connection_mapping_for_extranonce.write().await;
                        let old_extranonce = conn_map.upstream_extranonce1.as_ref();
                        let changed =
                            old_extranonce.is_some() && old_extranonce != Some(&extranonce1);

                        if changed {
                            warn!(
                                old = ?old_extranonce,
                                new = %extranonce1,
                                "Extranonce changed - disconnecting all miners"
                            );

                            // Disconnect miners
                            let peers: Vec<String> =
                                conn_map.get_channels().keys().cloned().collect();

                            warn!(
                                count = peers.len(),
                                "Disconnecting all miners due to extranonce change"
                            );
                            for peer_addr in peers {
                                conn_map.disconnect_peer(&peer_addr, "Upstream extranonce changed");
                            }
                        }

                        // Update the state, this guarantees that the next miner to grab the lock sees the new extranonce
                        conn_map.set_upstream_extranonce(extranonce1, extranonce2_size);
                        drop(conn_map);

                        // Signal ready only on first connection
                        if let Some(tx) = ready_tx.take() {
                            if let Err(_) = tx.send(()) {
                                warn!("Failed to signal upstream ready (receiver dropped)");
                            } else {
                                info!("Signaled upstream ready to main thread");
                            }
                        }
                        debug!("Stratum server updated with upstream extranonce");
                    }
                    debug!("Extranonce handler exiting for this connection");
                });

                // Spawn difficulty handler for this connection
                let connection_mapping_for_difficulty = connection_mapping_for_upstream.clone();
                let difficulty_task = tokio::spawn(async move {
                    while let Some(difficulty) = upstream_difficulty_rx.recv().await {
                        info!("Received upstream difficulty: {}", difficulty);
                        let mut conn_map = connection_mapping_for_difficulty.write().await;
                        conn_map.set_upstream_difficulty(difficulty);
                        drop(conn_map);
                        debug!("Stratum server updated with upstream difficulty");
                    }
                    debug!("Difficulty handler exiting for this connection");
                });

                let upstream_client = upstream_pool::UpstreamPoolClient::new(
                    upstream_config.clone(),
                    upstream_share_rx.clone(),
                    upstream_job_tx.clone(),
                    notification_tx_for_upstream_difficulty.clone(),
                    upstream_response_tx.clone(),
                    Some(upstream_extranonce_tx),
                    Some(upstream_difficulty_tx),
                    configure_rx.clone(),
                    upstream_cache_clone.clone(),
                    audit_log_tx.clone(),
                    audit_dag.clone(),
                );

                // Mark upstream as connected
                {
                    let mut conn_map = connection_mapping_for_upstream.write().await;
                    conn_map.set_upstream_connected(true);
                }

                // Run the client with cancellation support
                let result = tokio::select! {
                    result = upstream_client.run() => result,
                    _ = upstream_task_token.cancelled() => {
                        info!("Upstream client received shutdown signal during connection");
                        // Return Ok to break the reconnection loop gracefully
                        Ok(())
                    }
                };

                // Mark upstream as disconnected
                {
                    let mut conn_map = connection_mapping_for_upstream.write().await;
                    conn_map.set_upstream_connected(false);
                }

                // Cleanup per-connection tasks
                extranonce_task.abort();
                difficulty_task.abort();

                // Invalidate cached job on disconnect
                {
                    let mut cache = upstream_cache_clone.write().await;
                    cache.invalidate_job();
                    info!("Invalidated cached job due to upstream disconnect");
                }

                match result {
                    Ok(_) => {
                        warn!("Upstream pool client exited gracefully");

                        // If cancelled, break immediately
                        if upstream_task_token.is_cancelled() {
                            break;
                        }
                        break;
                    }
                    Err(e) => {
                        error!("Upstream pool client error: {:?}", e);

                        // Check if shutdown was triggered before retrying
                        if upstream_task_token.is_cancelled() {
                            info!("Shutdown requested, stopping upstream reconnection");
                            break;
                        }
                        info!("Invalidating all upstream jobs to prevent stale shares...");
                        global_job_store_for_upstream_cleanup
                            .lock()
                            .await
                            .clear_upstream_jobs();
                        info!("Upstream job cache cleared.");

                        // Calculate backoff delay with jitter
                        let delay = std::cmp::min(
                            base_delay * 2u32.saturating_pow(retry_count.min(6)),
                            max_delay,
                        );
                        let jitter = Duration::from_millis(rand::random::<u64>() % 1000);
                        let total_delay = delay + jitter;
                        error!(
                            "Upstream connection lost - reconnecting in {:?} (attempt #{})",
                            total_delay,
                            retry_count + 1
                        );
                        tokio::select! {
                            _ = tokio::time::sleep(total_delay) => {
                                // Normal sleep completed
                            }
                            _ = upstream_task_token.cancelled() => {
                                info!("Shutdown requested during reconnection backoff");
                                break;
                            }
                        }
                        retry_count += 1;

                        // Reset retry count if we've been connected successfully for a while
                        if last_successful_connection.elapsed() > Duration::from_secs(300) {
                            info!("Resetting retry count due to previous stable connection");
                            retry_count = 0;
                        }
                        last_successful_connection = std::time::Instant::now();
                    }
                }
            }

            info!("Upstream pool client task shutting down");
        });

        (
            Some(upstream_share_tx),
            Some(configure_tx),
            Some(audit_dag_for_stratum),
            audit_dag_for_notifier_inner,
        )
    } else {
        info!("Audit mode disabled, running in normal pool mode");
        (None, None, None, None)
    };

    if args.audit {
        info!("Waiting for upstream pool (timeout: 30s)...");
        match tokio::time::timeout(Duration::from_secs(60), upstream_ready_rx).await {
            // Changed from 30s
            Ok(Ok(())) => {
                info!("Upstream pool connected successfully");
            }
            Ok(Err(_)) => {
                error!("Upstream ready channel closed unexpectedly");
                std::process::exit(1);
            }
            Err(_) => {
                error!("Upstream pool failed to connect within 60 seconds");
                error!("Check --upstream-host, --upstream-username, and network connectivity");
                error!("Process will exit and should be restarted by user");
                std::process::exit(1);
            }
        }
        info!("Upstream reconnection monitoring active, will auto-reconnect on disconnects");
    }

    //Running the notification service
    tokio::spawn(async move {
        let _res = notifier
            .run_notifier(
                connection_mapping.clone(),
                &mut latest_template_ref,
                &mut latest_template_merkle_branch_ref,
                latest_template_id_for_notifier,
                upstream_cache_for_notifier,
                audit_dag_for_notifier,
            )
            .await;
    });
    //Running the stratum service
    let spin_lock_ref = ibd_spinlock.clone();
    tokio::spawn(async move {
        let _res = stratum_server
            .run_stratum_service(
                stratum_listener,
                global_job_store,
                notification_tx_clone,
                swarm_handler_arc.clone(),
                spin_lock_ref,
                audit_dag_option,
                upstream_share_tx_option,
                upstream_configure_tx_option,
            )
            .await;
    });

    let keystore_path = datadir_path.join("keystore");
    #[cfg(unix)]
    {
        if keystore_path.exists() {
            let perms = fs::metadata(&keystore_path)?.permissions();
            if perms.mode() & 0o777 != 0o400 {
                warn!(
                    permissions = perms.mode() & 0o777,
                    "Keystore permissions are not secure, setting to 0o400"
                );
                let mut new_perms = perms.clone();
                new_perms.set_mode(0o400);
                fs::set_permissions(&keystore_path, new_perms)?;
            }
        }
    }
    let keypair = match fs::read(&keystore_path) {
        Ok(keypair) => {
            info!(path = %keystore_path.display(), "Loading keypair from keystore");
            libp2p::identity::Keypair::from_protobuf_encoding(&keypair).map_err(|e| {
                error!(error = %e, path = %keystore_path.display(), "Failed to read keypair from keystore");
                e
            })?
        }
        Err(_) => {
            info!(path = %keystore_path.display(), "Generating new keypair");
            let keypair: Keypair = libp2p::identity::Keypair::generate_ed25519();
            let keypair_bytes = keypair.to_protobuf_encoding()?;
            fs::write(&keystore_path, keypair_bytes)?;
            #[cfg(unix)]
            {
                let mut perms = fs::metadata(&keystore_path)?.permissions();
                perms.set_mode(0o400);
                fs::set_permissions(&keystore_path, perms)?;
                info!(path = %keystore_path.display(), perms = "0o400", "Set keystore permissions");
            }
            keypair
        }
    };
    // load beads from db (if present) and insert in braid here
    // Initializing the peer manager (shared between swarm and RPC server)
    // Using RwLock to allow concurrent reads (RPC server) while swarm handler can write
    let peer_manager_arc = Arc::new(tokio::sync::RwLock::new(PeerManager::new(8)));
    //For local testing uncomment this keypair peer since it running to process will
    //result in same peerID leading to OutgoingConnectionError
    // let keypair = identity::Keypair::generate_ed25519();
    //IPC(inter process communication) based `getblocktemplate` and `notification` to send to the downstream via the `cmempoold` architecture
    info!(socket = %args.ipc_socket, "IPC socket path");

    // Spawn IPC handler
    let _ipc_handler = if !args.audit {
        Some(tokio::task::spawn_blocking(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("Failed to create tokio runtime");
            rt.block_on(async {
            let local_set = tokio::task::LocalSet::new();

            local_set
                .run_until(async {
                    let template_cache: Arc<
                        tokio::sync::Mutex<
                            HashMap<TemplateId, Arc<node::ipc::client::BlockTemplate>>,
                        >,
                    > = Arc::new(tokio::sync::Mutex::new(HashMap::new()));
                    let template_cache_for_consumer = template_cache.clone();
                    let template_cache_for_listener = template_cache.clone();
                    let (ipc_template_tx, ipc_template_rx) =
                        tokio::sync::mpsc::channel::<Arc<node::ipc::client::BlockTemplate>>(1);

                    let listener_task = tokio::task::spawn_local({
                        let ipc_socket_path = ipc_socket_path_for_blocking.clone();
                        let ipc_template_tx = ipc_template_tx.clone();
                        let template_cache = template_cache_for_listener.clone();
                        let network = network_for_ipc;
                        let rpc_command_rx = rpc_proxy_rx;

                        async move {
                            match node::ipc::ipc_block_listener(
                                ipc_socket_path,
                                ipc_template_tx,
                                network,
                                template_cache,
                                block_submission_rx,
                                rpc_command_rx,
                            )
                            .await
                            {
                                Ok(_) => {
                                    info!("IPC block listener exited");
                                }
                                Err(e) => {
                                    error!(error = %e, "IPC block listener error");
                                }
                            }
                        }
                    });

                    let consumer_task = tokio::task::spawn_local({
                        async move {
                            if let Err(e) = ipc_template_consumer(
                                ipc_template_rx,
                                notification_tx_for_ipc,
                                &mut latest_template_for_ipc.clone(),
                                &mut latest_template_merkle_branch_for_ipc.clone(),
                                template_cache_for_consumer,
                                latest_template_id_for_consumer,
                            )
                            .await
                            {
                                error!(error = ?e, "IPC template consumer error");
                            }
                        }
                    });

                    tokio::select! {
                        _ = listener_task => info!(task = "listener", "IPC listener task completed"),
                        _ = consumer_task => info!(task = "consumer", "Template consumer task completed"),
                        _ = ipc_task_token.cancelled() => {
                            info!("IPC task shutting down - cancellation token triggered");
                        }
                    }
                })
                .await;
        });
        }))
    } else {
        info!("Skipping IPC connection, audit mode enabled using upstream pool jobs");
        None
    };
    let swarm_handle = if !args.audit {
        //Default listening addr of spawned peer
        let bind_addr = parse_bind_address(&args.bind, DEFAULT_P2P_PORT)?;
        let swarm_config = SwarmConfig::new(keypair, bind_addr);
        let listen_addr = swarm_config.to_multiaddr()?;
        //Building swarm with `BraidpoolBeahaviour`
        let mut swarm = build_swarm(swarm_config).await?;

        // Bootstrap the swarm
        let topic = floodsub::Topic::new(BRAIDPOOL_TOPIC);
        setup_and_bootstrap(&mut swarm, listen_addr, topic)?;

        // Dial additional nodes if provided
        //This should be changed to a single dial function only
        if let Some(addnode) = &args.addnode {
            dial_additional_nodes(&mut swarm, addnode);
        }
        //Swarm context shared as reference among different handlers and task but keeping the Swarm centralized
        let ctx = SwarmContext::new(
            braid.clone(),
            db_tx,
            ibd_command_tx,
            ibd_spinlock.clone(),
            peer_manager_arc.clone(),
            swarm_command_sender,
            dashboard_notifier,
        );
        //Event loop for p2p related events
        tokio::spawn(async move {
            p2p_event_loop::run(ctx, swarm, swarm_command_receiver).await;
        })
    } else {
        info!("Skipping P2P swarm, audit mode enabled");
        tokio::spawn(async {}) // dummy handler for the shutdown abort() call
    };

    //graceful shutdown via `Cancellation token`
    let shutdown_signal = tokio::signal::ctrl_c().await;
    match shutdown_signal {
        Ok(_) => {
            info!(component = "shutdown", "Graceful shutdown initiated");
            info!(
                component = "stratum",
                "Disconnecting all miners gracefully..."
            );
            {
                let mut conn_map = connection_mapping_for_shutdown.write().await;
                let miner_count = conn_map.get_channels().len();
                info!(miners = miner_count, "Sending shutdown notice to miners");
                conn_map
                    .disconnect_all_with_message("Pool server restarting")
                    .await;
            }

            // Cancel all audit mode tasks first
            info!(component = "audit", "Cancelling upstream pool tasks");
            main_task_token.cancel();

            info!(component = "database", "Closing connection pool");
            if let Some(pool_arc) = optional_db_pool {
                // Closing all the existing connections to pool and committing from .db-wal to .db
                pool_arc.close().await;
                info!(component = "database", "Connections closed");
            }
            // Give tasks time to drain
            tokio::time::sleep(Duration::from_millis(100)).await;

            info!(component = "swarm", "Shutting down network swarm");
            swarm_handle.abort();
            tokio::time::sleep(Duration::from_millis(1)).await;
            #[allow(unused)]
            let shutdown_sub_tasks = match main_shutdown_tx
                .send(tokio::signal::unix::SignalKind::interrupt())
                .await
            {
                Ok(_) => {
                    info!(
                        component = "shutdown",
                        "Sub-tasks interrupted - waiting for graceful shutdown"
                    );
                    main_task_token.cancel();
                }
                Err(error) => {
                    error!(error = ?error, "Failed to send interrupt signal to sub-tasks");
                }
            };
        }
        Err(error) => {
            error!(
                error = ?error,
                component = "shutdown",
                "Shutdown signal error"
            );
        }
    }

    Ok(())
}
