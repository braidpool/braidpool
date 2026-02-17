use bitcoin::Network;
use clap::Parser;
use futures::lock::Mutex;
use libp2p::{floodsub, identity::Keypair};
use node::{
    behaviour::BRAIDPOOL_TOPIC,
    braid, cli,
    db::db_handlers::{fetch_beads_in_batch, DBHandler},
    ibd_manager::{IBDManager, IBD_TRIGGER_AFTER},
    ipc_template_consumer,
    peer_manager::PeerManager,
    rpc_server::{run_rpc_server, BitcoinRpcConfig, RpcProxyCommand},
    setup_tracing,
    stratum::{BlockTemplate, ConnectionMapping, Notifier, NotifyCmd, Server, StratumServerConfig},
    swarm::{
        bootstrap::{dial_additional_nodes, setup_and_bootstrap},
        builder::{build_swarm, parse_bind_address, SwarmConfig},
        config::DEFAULT_P2P_PORT,
        p2p_event_loop, SwarmContext,
    },
    SwarmCommand, SwarmHandler, TemplateId,
};
use std::{
    collections::HashMap,
    error::Error,
    fs,
    path::Path,
    sync::{atomic::AtomicBool, Arc},
    time::Duration,
};
use tokio::sync::{mpsc, RwLock};
use tokio_util::sync::CancellationToken;
use tracing::{debug, error, info, warn};

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // Initialize tracing
    setup_tracing()?;
    //Parsing args
    let args = cli::Cli::parse();
    //IBD manager for ibd handling
    let (mut ibd_manager, ibd_command_tx) = IBDManager::new();
    let _ibd_handler = tokio::spawn(async move {
        ibd_manager.run_ibd_handler().await;
    });

    // IBD flag - true at start (will be in IBD by default)
    let ibd_spinlock = Arc::new(AtomicBool::new(true));
    //Local braid instance being shared across different tasks
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(Vec::from([]))));
    //DB task handler for persistant of beads onto disk
    let (mut _db_handler, db_tx) = DBHandler::new().await.map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Database initialization failed: {:?}", e),
        )
    })?;
    let db_connection_pool = _db_handler.db_connection_pool.clone();

    // Load beads from database
    let db_connection_pool_ref = _db_handler.db_connection_pool.clone();
    let braid_ref = braid.clone();
    //Fetching beads from disk before initializing other tasks to pre-shutdown state
    let initial_bead_fetch_handle = tokio::spawn(async move {
        let mut guard = braid_ref.write().await;
        let fetched_beads = fetch_beads_in_batch(db_connection_pool_ref, 50).await?;
        info!(beads = fetched_beads.len(), "Beads loaded from DB");
        for bead in &fetched_beads {
            let status = guard.extend(bead);
            debug!(hash = ?bead.block_header.block_hash(), status = ?status, "Bead inserted");
        }
        Ok::<(), node::error::DBErrors>(())
    });

    match initial_bead_fetch_handle.await {
        Ok(Ok(())) => info!("Initial bead fetch completed"),
        Ok(Err(e)) => {
            error!(error = ?e, "Failed to fetch beads from DB");
            return Err(format!("Database bead fetch failed: {:?}", e).into());
        }
        Err(e) => {
            error!(error = ?e, "Initial bead fetch task panicked");
            return Err(format!("Initial bead fetch task panicked: {}", e).into());
        }
    }

    // Start DB query handler
    tokio::spawn(async move {
        let _res = _db_handler.insert_query_handler().await;
    });

    let latest_template_id = Arc::new(Mutex::new(TemplateId::default()));
    let latest_template_id_for_notifier = latest_template_id.clone();
    let latest_template_id_for_consumer = latest_template_id.clone();
    //Initial template being shared across the notification task and swarm_handler task
    let latest_template = Arc::new(Mutex::new(BlockTemplate::default()));
    let latest_template_merkle_branch = Arc::new(Mutex::new(Vec::new()));
    let mut latest_template_ref = latest_template.clone();
    let mut latest_template_merkle_branch_ref = latest_template_merkle_branch.clone();

    let (notification_tx, notification_rx) = mpsc::channel::<NotifyCmd>(1024);
    //Swarm handler for additional event other than p2p events related to swarm
    let (swarm_handler, swarm_command_receiver) =
        SwarmHandler::new(Arc::clone(&braid), db_tx.clone());
    let swarm_command_sender = swarm_handler.command_sender.clone();
    let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));

    let notification_tx_clone = notification_tx.clone();
    //Global connection mapping for each downstream connected to stratum server along with their respective sender channels
    let connection_mapping = Arc::new(tokio::sync::RwLock::new(ConnectionMapping::new()));
    // Clone connection_mapping for RPC server before it's used in async move blocks
    let connection_mapping_for_rpc = Arc::clone(&connection_mapping);
    //Global mining mapping mapping peer to its jobs provided by upstream uptill now
    let mining_job_map = Arc::new(Mutex::new(HashMap::new()));
    //Notifier task for providing jobs to downstream
    let mut notifier = Notifier::new(notification_rx, Arc::clone(&mining_job_map));
    let stratum_config = StratumServerConfig::default();
    //Block submission channel after validation of PoW to bitcoin-node
    let (block_submission_tx, block_submission_rx) =
        tokio::sync::mpsc::unbounded_channel::<node::stratum::BlockSubmissionRequest>();

    // IBD trigger task
    let swarm_cmd_for_ibd = swarm_command_sender.clone();
    let _ibd_trigger_handler = tokio::spawn(async move {
        tokio::time::sleep(Duration::from_secs(IBD_TRIGGER_AFTER)).await;
        if let Err(e) = swarm_cmd_for_ibd.send(SwarmCommand::InitiateIBD).await {
            error!(error = ?e, "Failed to initiate IBD");
        } else {
            info!("IBD trigger sent");
        }
    });

    // Start stratum server
    let mut stratum_server = Server::new(
        stratum_config,
        connection_mapping.clone(),
        Some(block_submission_tx),
    );

    // Run notifier
    tokio::spawn(async move {
        let _res = notifier
            .run_notifier(
                connection_mapping.clone(),
                &mut latest_template_ref,
                &mut latest_template_merkle_branch_ref,
                latest_template_id_for_notifier,
            )
            .await;
    });

    // Run stratum service
    let ibd_flag_for_stratum = ibd_spinlock.clone();
    tokio::spawn(async move {
        let _res = stratum_server
            .run_stratum_service(
                mining_job_map,
                notification_tx_clone,
                swarm_handler_arc.clone(),
                ibd_flag_for_stratum,
            )
            .await;
    });

    let (main_shutdown_tx, _main_shutdown_rx) =
        mpsc::channel::<tokio::signal::unix::SignalKind>(32);
    let main_task_token = CancellationToken::new();
    let ipc_task_token = main_task_token.clone();


    let datadir_str = args.datadir.to_str().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid datadir path encoding",
        )
    })?;
    let datadir = shellexpand::full(datadir_str).map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("Shell expansion failed: {}", e),
        )
    })?;

    // Create data directory if needed
    match fs::metadata(&*datadir) {
        Ok(m) if !m.is_dir() => {
            error!(datadir = %datadir, "Data directory exists but is not a directory");
        }
        Ok(_) => {
            info!(datadir = %datadir, "Using existing data directory");
        }
        Err(_) => {
            info!(datadir = %datadir, "Creating data directory");
            fs::create_dir_all(&*datadir)?;
        }
    }

    let datadir_path = Path::new(&*datadir);
    let keystore_path = datadir_path.join("keystore");

    #[cfg(unix)]
    {
        if keystore_path.exists() {
            let perms = fs::metadata(&keystore_path)?.permissions();
            if perms.mode() & 0o777 != 0o400 {
                warn!(
                    perms = perms.mode() & 0o777,
                    "Keystore permissions not secure, fixing"
                );
                let mut new_perms = perms.clone();
                new_perms.set_mode(0o400);
                fs::set_permissions(&keystore_path, new_perms)?;
            }
        }
    }
    //Generating ed25519 curve keypair for unique PeerId during initialization
    let keypair = match fs::read(&keystore_path) {
        Ok(bytes) => {
            info!(path = %keystore_path.display(), "Loading keypair from keystore");
            Keypair::from_protobuf_encoding(&bytes).map_err(|e| {
                error!(error = %e, "Failed to read keypair");
                e
            })?
        }
        Err(_) => {
            info!(path = %keystore_path.display(), "Generating new keypair");
            let keypair = Keypair::generate_ed25519();
            let bytes = keypair.to_protobuf_encoding()?;
            fs::write(&keystore_path, bytes)?;

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
    // Initializing the peer manager (shared between swarm and RPC server)
    // Using RwLock to allow concurrent reads (RPC server) while swarm handler can write
    let peer_manager_arc = Arc::new(tokio::sync::RwLock::new(PeerManager::new(8)));
    //For local testing uncomment this keypair peer since it running to process will
    //result in same peerID leading to OutgoingConnectionError
    // let keypair = identity::Keypair::generate_ed25519();
    //Configured network
    let network = if let Some(network_name) = &args.network {
        info!(network = %network_name, "Network selected");
        match network_name.as_str() {
            "main" | "mainnet" => Network::Bitcoin,
            "testnet" | "testnet4" => Network::Testnet(bitcoin::TestnetVersion::V4),
            "signet" => Network::Signet,
            "regtest" => Network::Regtest,
            "cpunet" => Network::CPUNet,
            _ => {
                error!(network = %network_name, "Invalid network");
                info!("Using fallback: regtest");
                Network::Regtest
            }
        }
    } else {
        Network::Bitcoin
    };
    //IPC node initializer including our capnp client
    let ipc_socket_path = args.ipc_socket.clone();
    let notification_tx_for_ipc = notification_tx.clone();
    let latest_template_for_ipc = latest_template.clone();
    let latest_template_merkle_branch_for_ipc = latest_template_merkle_branch.clone();

    // Create RPC proxy command channel - sender goes to RPC server, receiver goes to IPC handler
    let (rpc_proxy_tx, rpc_proxy_rx) = tokio::sync::mpsc::unbounded_channel::<RpcProxyCommand>();
    // peer_manager_arc is created above and shared between swarm and RPC server
    //spawning the rpc server
    let rpc_addr = "127.0.0.1:6682"; // TODO: Load from config file
    let bitcoin_rpc_config = BitcoinRpcConfig::from_cli_args(&args).unwrap_or_else(|e| {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    });
    let server_join = tokio::spawn(run_rpc_server(
        Arc::clone(&braid),
        rpc_addr,
        peer_manager_arc.clone(),
        connection_mapping_for_rpc.clone(),
        latest_template.clone(),
        rpc_proxy_tx,
        bitcoin_rpc_config,
    ));
    match server_join.await {
        Ok(Ok(_addr)) => {}
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

    info!(socket = %ipc_socket_path, "IPC socket path");

    let _ipc_handler = tokio::task::spawn_blocking(move || {
        let rt = match tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
        {
            Ok(rt) => rt,
            Err(e) => {
                error!(error = %e, "Failed to create tokio runtime for IPC");
                return;
            }
        };

        rt.block_on(async {
            let local_set = tokio::task::LocalSet::new();
            local_set
                .run_until(async {
                    let template_cache: Arc<
                        tokio::sync::Mutex<
                            HashMap<TemplateId, Arc<node::ipc::client::BlockTemplate>>,
                        >,
                    > = Arc::new(tokio::sync::Mutex::new(HashMap::new()));

                    let (ipc_template_tx, ipc_template_rx) =
                        tokio::sync::mpsc::channel::<Arc<node::ipc::client::BlockTemplate>>(1);

                    let listener_task = tokio::task::spawn_local({
                        let ipc_socket = ipc_socket_path.clone();
                        let tx = ipc_template_tx.clone();
                        let cache = template_cache.clone();
                        let rpc_command_rx = rpc_proxy_rx;
                        async move {
                            match node::ipc::ipc_block_listener(
                                ipc_socket,
                                tx,
                                network,
                                cache,
                                block_submission_rx,
                                rpc_command_rx,
                            )
                            .await
                            {
                                Ok(_) => info!("IPC listener exited"),
                                Err(e) => error!(error = %e, "IPC listener error"),
                            }
                        }
                    });

                    let consumer_task = tokio::task::spawn_local({
                        let cache = template_cache.clone();
                        async move {
                            if let Err(e) = ipc_template_consumer(
                                ipc_template_rx,
                                notification_tx_for_ipc,
                                &mut latest_template_for_ipc.clone(),
                                &mut latest_template_merkle_branch_for_ipc.clone(),
                                cache,
                                latest_template_id_for_consumer,
                            )
                            .await
                            {
                                error!(error = ?e, "IPC consumer error");
                            }
                        }
                    });

                    tokio::select! {
                        _ = listener_task => info!("IPC listener completed"),
                        _ = consumer_task => info!("IPC consumer completed"),
                        _ = ipc_task_token.cancelled() => info!("IPC cancelled"),
                    }
                })
                .await;
        });
    });
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
    if let Some(addnode) = args.addnode {
        dial_additional_nodes(&mut swarm, &addnode);
    }
    //Swarm context shared as reference among different handlers and task but keeping the Swarm centralized
    let ctx = SwarmContext::new(
        braid.clone(),
        db_tx,
        ibd_command_tx,
        ibd_spinlock.clone(),
        peer_manager_arc.clone(),
        swarm_command_sender,
    );
    //Event loop for p2p related events
    let swarm_handle = tokio::spawn(async move {
        p2p_event_loop::run(ctx, swarm, swarm_command_receiver).await;
    });

    //graceful shutdown via `Cancellation token`
    let shutdown_signal = tokio::signal::ctrl_c().await;
    match shutdown_signal {
        Ok(_) => {
            info!(component = "database", "Closing connection pool");
            let pool = db_connection_pool.lock().await;
            pool.close().await;
            info!(component = "database", "Connections closed");

            info!(component = "swarm", "Shutting down");
            swarm_handle.abort();
            tokio::time::sleep(Duration::from_millis(1)).await;

            if let Err(e) = main_shutdown_tx
                .send(tokio::signal::unix::SignalKind::interrupt())
                .await
            {
                error!(error = ?e, "Failed to send shutdown signal");
            } else {
                info!(component = "shutdown", "Graceful shutdown initiated");
                main_task_token.cancel();
            }
        }
        Err(e) => {
            error!(error = ?e, "Shutdown signal error");
        }
    }

    Ok(())
}
