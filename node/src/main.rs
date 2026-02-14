use bitcoin::consensus::encode::deserialize;
use bitcoin::Network;
use clap::Parser;
use futures::lock::Mutex;
use futures::StreamExt;
use libp2p::kad::BootstrapOk;
use libp2p::{
    core::multiaddr::Multiaddr,
    floodsub::{self},
    identify,
    identity::Keypair,
    kad::{self, Mode, QueryResult},
    ping, request_response,
    swarm::SwarmEvent,
    PeerId,
};
use node::db::db_handlers::{fetch_beads_in_batch, prepare_bead_tuple_data};
use node::ibd_manager::{IBD_TRIGGER_AFTER, MAX_IBD_INCOMING_THRESHOLD, MAX_IBD_RETRIES};
use node::utils::BeadHash;
use node::SwarmHandler;
use node::{
    bead::{Bead, BeadHashes, BeadRequest, BeadResponse, BeadSyncError},
    behaviour::{self, BEAD_ANNOUNCE_PROTOCOL, BRAIDPOOL_TOPIC},
    braid, cli,
    db::db_handlers::DBHandler,
    ibd_manager::{IBDCommands, IBDManager, IBD_BATCH_SIZE},
    ipc_template_consumer,
    peer_manager::PeerManager,
    rpc_server::{parse_arguments, run_rpc_server},
    setup_tracing,
    stratum::{BlockTemplate, ConnectionMapping, Notifier, NotifyCmd, Server, StratumServerConfig},
    SwarmCommand, TemplateId,
};
use std::collections::HashSet;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};
use std::{collections::HashMap, error::Error};
use std::{fs, time::Duration};
use tokio_util::sync::CancellationToken;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

use behaviour::{BraidPoolBehaviour, BraidPoolBehaviourEvent};

use crate::behaviour::KADPROTOCOLNAME;
const LATENCY_ALPHA: u64 = 10; // seconds
                               //boot nodes peerIds
const BOOTNODES: [&str; 1] = ["12D3KooWG9z8TziaNuYyEcc9FeUC3FTtrEf2XSnSdDpLvx4Jh2w3"];
//dns NS
const SEED_DNS: &str = "/dnsaddr/french.braidpool.net";
//combined addr for dns resolution and dialing of boot for peer discovery
const ADDR_REFRENCE: &str =
    "/dnsaddr/french.braidpool.net/p2p/12D3KooWG9z8TziaNuYyEcc9FeUC3FTtrEf2XSnSdDpLvx4Jh2w3";
use tokio::sync::{
    mpsc::{self},
    RwLock,
};
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // Initialize tracing with colors and module prefixes
    setup_tracing()?;
    let (mut ibd_manager, ibd_command_tx) = IBDManager::new();
    //IBD cache handler
    let _ibd_handler = tokio::spawn(async move {
        ibd_manager.run_ibd_handler().await;
    });
    //False if not under ibd otherwise true at start will be in IBD by default
    let ibd_or_not: AtomicBool = AtomicBool::new(true);
    let ibd_spinlock = Arc::new(ibd_or_not);
    // Initializing the braid object with read write lock
    //for supporting concurrent readers and single writer
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(Vec::from([]))));
    //Initializing DB and db command handler
    let (mut _db_handler, db_tx) = DBHandler::new().await.map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Database initialization failed: {:?}", e),
        )
    })?;
    let db_connection_pool = _db_handler.db_connection_pool.clone();
    //Reconstructing local braid upon startup
    let db_connection_pool_ref = _db_handler.db_connection_pool.clone();
    let braid_ref = braid.clone();
    // FIXME instead we should look 144 blocks back from the bitcoin tip (1 day) and load beads
    // starting from that block as genesis
    let initial_bead_fetch_handle = tokio::spawn(async move {
        let mut guard = braid_ref.write().await;
        let fetched_beads = fetch_beads_in_batch(db_connection_pool_ref, 1000).await?;
        for bead in &fetched_beads {
            let curr_bead_status = guard.extend(&bead);
            debug!(
                hash = ?bead.block_header.block_hash(),
                status = ?curr_bead_status,
                "Bead inserted"
            );
        }
        info!(beads = fetched_beads.len(), "Beads loaded from DB");
        Ok::<(), node::error::DBErrors>(())
    });
    match initial_bead_fetch_handle.await {
        Ok(Ok(())) => {
            info!("Initial bead fetch completed successfully");
        }
        Ok(Err(e)) => {
            error!(error = ?e, "Failed to fetch beads from DB during startup");
            return Err(format!("Database bead fetch failed: {:?}", e).into());
        }
        Err(e) => {
            error!(error = ?e, "Initial bead fetch task panicked");
            return Err(format!("Initial bead fetch task panicked: {}", e).into());
        }
    }
    let latest_template_id = Arc::new(Mutex::new(TemplateId::default()));
    let latest_template_id_for_notifier = latest_template_id.clone();
    let latest_template_id_for_consumer = latest_template_id.clone();
    //Starting the `query_handler` task
    tokio::spawn(async move {
        let _res = _db_handler.insert_query_handler().await;
    });
    //latest available template to be cached for the newest connection until new job is received
    let latest_template = Arc::new(Mutex::new(BlockTemplate::default()));
    //latest available template merkle branch
    let latest_template_merkle_branch = Arc::new(Mutex::new(Vec::new()));
    let mut latest_template_ref = latest_template.clone();
    let mut latest_template_merkle_branch_ref = latest_template_merkle_branch.clone();
    //One will go into the IPC and the other will go to the `notifier`
    let (notification_tx, notification_rx) = mpsc::channel::<NotifyCmd>(1024);
    //Communication bridge between stratum and network swarm and swarm commands also, for communicating share population and propogating them further
    let (swarm_handler, mut swarm_command_receiver) =
        SwarmHandler::new(Arc::clone(&braid), db_tx.clone());
    //Swarm command sender
    let swarm_command_sender = swarm_handler.command_sender.clone();
    let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
    //cloning the channel to be sent across different interfaces
    let notification_tx_clone = notification_tx.clone();
    //Connection mapping for all the downstream connection connected to the stratum server
    let connection_mapping = Arc::new(Mutex::new(ConnectionMapping::new()));
    //Mining job map keeping all the jobs provided to the downstream
    let mining_job_map = Arc::new(Mutex::new(HashMap::new()));
    //Intializing `notifier` for mining.notify
    let mut notifier: Notifier = Notifier::new(notification_rx, Arc::clone(&mining_job_map));
    //Stratum configuration initialization
    let stratum_config: StratumServerConfig = StratumServerConfig::default();
    let (block_submission_tx, block_submission_rx) =
        tokio::sync::mpsc::unbounded_channel::<node::stratum::BlockSubmissionRequest>();
    //IBD notifier task after peer_discovery
    let swarm_command_sender_ref = swarm_command_sender.clone();
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
    //Initializing stratum server
    let mut stratum_server = Server::new(
        stratum_config,
        connection_mapping.clone(),
        Some(block_submission_tx),
    );
    //Running the notification service
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
    //Running the stratum service
    let spin_lock_ref = ibd_spinlock.clone();
    tokio::spawn(async move {
        let _res = stratum_server
            .run_stratum_service(
                mining_job_map,
                notification_tx_clone,
                swarm_handler_arc.clone(),
                spin_lock_ref,
            )
            .await;
    });

    let (main_shutdown_tx, _main_shutdown_rx) =
        mpsc::channel::<tokio::signal::unix::SignalKind>(32);
    let main_task_token = CancellationToken::new();
    let ipc_task_token = main_task_token.clone();
    let args = cli::Cli::parse();
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
    match fs::metadata(&*datadir) {
        Ok(m) => {
            if !m.is_dir() {
                error!(datadir = %datadir, "Data directory exists but is not a directory");
            }
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
                    permissions = perms.mode() & 0o777,
                    "Keystore permissions are not secure, setting to 0o400"
                );
                let mut new_perms = perms.clone();
                new_perms.set_mode(0o400);
                fs::set_permissions(&keystore_path, new_perms)?;
            }
        }
    }
    //for local testing comment this loading of keypair from keystore
    //and use the below one
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
    //spawning the rpc server
    let rpc_addr = "127.0.0.1:6682"; // TODO: Load from config file
    if let Some(rpc_command) = args.command {
        let server_address = tokio::spawn(run_rpc_server(Arc::clone(&braid), rpc_addr));
        let socket_address = server_address
            .await
            .map_err(|e| {
                std::io::Error::new(
                    std::io::ErrorKind::Other,
                    format!("RPC server task failed: {}", e),
                )
            })?
            .map_err(|_| {
                std::io::Error::new(std::io::ErrorKind::Other, "RPC server startup failed")
            })?;
        let _parsing_handle =
            tokio::spawn(parse_arguments(rpc_command, socket_address.clone())).await;
    } else {
        //running the rpc server and updating the reference counter
        //for shared ownership
        let _server_handler = tokio::spawn(run_rpc_server(Arc::clone(&braid), rpc_addr)).await;
    }
    // load beads from db (if present) and insert in braid here
    // Initializing the peer manager
    let mut peer_manager = PeerManager::new(8);
    //For local testing uncomment this keypair peer since it running to process will
    //result in same peerID leading to OutgoingConnectionError

    // let keypair = identity::Keypair::generate_ed25519();
    //creating a main topic subscribing to the current test topic
    let current_broadcast_topic: floodsub::Topic = floodsub::Topic::new(BRAIDPOOL_TOPIC);

    let swarm_builder = libp2p::SwarmBuilder::with_existing_identity(keypair)
        .with_tokio()
        .with_quic()
        .with_dns()
        .map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("DNS setup failed: {:?}", e),
            )
        })?;
    // Note: with_behaviour closure must return behaviour directly (not Result), using expect for clear error message
    let mut swarm = swarm_builder
        .with_behaviour(|local_key| {
            BraidPoolBehaviour::new(local_key).expect(
                "Failed to create BraidPoolBehaviour - check keypair and network configuration",
            )
        })?
        .with_swarm_config(|cfg| cfg.with_idle_connection_timeout(Duration::from_secs(u64::MAX)))
        .build();
    let socket_addr: std::net::SocketAddr = match args.bind.parse() {
        Ok(addr) => addr,
        Err(_) => format!("{}:6680", args.bind).parse().map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("Failed to parse bind address: {}", e),
            )
        })?,
    };
    let multi_addr: Multiaddr = format!(
        "/ip4/{}/udp/{}/quic-v1",
        socket_addr.ip(),
        socket_addr.port()
    )
    .parse()
    .map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("Failed to create multiaddress: {}", e),
        )
    })?;
    //subscribing to the braidpool topic for broadcasting bead_found and other peer_communications belonging to a particular topic
    swarm
        .behaviour_mut()
        .bead_announce
        .subscribe(current_broadcast_topic.clone());
    //setting the server mode for the kademlia apart from the server
    swarm.behaviour_mut().kademlia.set_mode(Some(Mode::Server));

    //adding the boot nodes for peer discovery
    swarm.listen_on(multi_addr.clone())?;
    for boot_peer in BOOTNODES {
        let peer_id = match boot_peer.parse::<PeerId>() {
            Ok(id) => id,
            Err(e) => {
                error!(boot_peer = %boot_peer, error = %e, "Failed to parse boot peer ID, skipping");
                continue;
            }
        };
        let seed_addr = match SEED_DNS.parse::<Multiaddr>() {
            Ok(addr) => addr,
            Err(e) => {
                error!(seed_dns = %SEED_DNS, error = %e, "Failed to parse seed DNS, skipping");
                continue;
            }
        };
        swarm
            .behaviour_mut()
            .kademlia
            .add_address(&peer_id, seed_addr);
    }
    info!(boot_node_count = %BOOTNODES.len(), "Boot nodes added to DHT");
    let boot_addr: Multiaddr = ADDR_REFRENCE.parse().map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("Failed to parse boot address: {}", e),
        )
    })?;
    swarm.dial(boot_addr)?;
    info!(address = %ADDR_REFRENCE, "Dialed boot node");
    //IPC(inter process communication) based `getblocktemplate` and `notification` to send to the downstream via the `cmempoold` architecture
    info!(socket = %args.ipc_socket, "IPC socket path");

    let network = if let Some(network_name) = &args.network {
        info!(network = %network_name, "Network selected");
        match network_name.as_str() {
            "main" | "mainnet" => Network::Bitcoin,
            "testnet" | "testnet4" => Network::Testnet(bitcoin::TestnetVersion::V4),
            "signet" => Network::Signet,
            "regtest" => Network::Regtest,
            "cpunet" => Network::CPUNet,
            _ => {
                error!(
                    network = %network_name,
                    valid_networks = "main, testnet, testnet4, signet, regtest, cpunet",
                    "Invalid network specified"
                );
                info!(fallback = "regtest", "Using fallback network");
                Network::Regtest
            }
        }
    } else {
        Network::Bitcoin
    };

    let ipc_socket_path_for_blocking = args.ipc_socket.clone();
    let notification_tx_for_ipc = notification_tx.clone();
    let latest_template_for_ipc = latest_template.clone();
    let latest_template_merkle_branch_for_ipc = latest_template_merkle_branch.clone();

    // Spawn IPC handler
    let _ipc_handler = tokio::task::spawn_blocking(move || {
        let rt = match tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
        {
            Ok(rt) => rt,
            Err(e) => {
                error!(error = %e, "Failed to create tokio runtime for IPC handler");
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
                    let template_cache_for_consumer = template_cache.clone();
                    let template_cache_for_listener = template_cache.clone();
                    let (ipc_template_tx, ipc_template_rx) =
                        tokio::sync::mpsc::channel::<Arc<node::ipc::client::BlockTemplate>>(1);

                    let listener_task = tokio::task::spawn_local({
                        let ipc_socket_path = ipc_socket_path_for_blocking.clone();
                        let ipc_template_tx = ipc_template_tx.clone();
                        let template_cache = template_cache_for_listener.clone();

                        async move {
                            match node::ipc::ipc_block_listener(
                                ipc_socket_path,
                                ipc_template_tx,
                                network,
                                template_cache,
                                block_submission_rx,
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
    });

    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            let node_multiaddr: Multiaddr = match node.parse() {
                Ok(addr) => addr,
                Err(e) => {
                    error!(node = %node, error = %e, "Failed to parse multiaddr, skipping");
                    continue;
                }
            };
            let dial_result = swarm.dial(node_multiaddr.clone());
            if let Some(err) = dial_result.err() {
                error!(address = %node_multiaddr, error = %err, "Failed to dial peer node");
                continue;
            }
            info!(address = %node_multiaddr, "Dialed peer node");
        }
    };
    let swarm_handle = tokio::spawn(async move {
        let braid = std::sync::Arc::clone(&braid);
        loop {
            tokio::select! {
             swarm_event = swarm.select_next_some()=>{
                 match swarm_event{
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Kademlia(
                         kad::Event::RoutingUpdated {
                             peer,
                             is_new_peer,
                             addresses,
                             bucket_range,
                             old_peer,
                         },
                     )) => {
                         info!(
                             peer = %peer,
                             is_new = %is_new_peer,
                             addresses = ?addresses,
                             bucket = ?bucket_range,
                             old_peer = ?old_peer,
                             "DHT routing updated"
                         );
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                         floodsub::FloodsubEvent::Subscribed { peer_id, topic },
                     )) => {
                         info!(
                             peer = ?peer_id,
                             topic = ?topic,
                             "Peer subscribed to topic"
                         );
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                         floodsub::FloodsubEvent::Unsubscribed { peer_id, topic },
                     )) => {
                         info!(
                             peer = ?peer_id,
                             topic = ?topic,
                             "Peer unsubscribed from topic"
                         );
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                         floodsub::FloodsubEvent::Message(message),
                     )) => {
                         info!(
                             topics = ?message.topics,
                             source = ?message.source,
                             size_bytes = %message.data.len(),
                             "Floodsub message received"
                         );
                         let result_bead: Result<Bead, bitcoin::consensus::DeserializeError> = deserialize(&message.data);
                         match result_bead {
                             Ok(bead) => {
                                info!(bead = ?bead, hash = %bead.block_header.block_hash(), "Received bead");
                                // Handle the received bead here
                                let mut braid_data = braid.write().await;
                                let status = {
                                     braid_data.extend(&bead)
                                 };
                                 if ibd_spinlock.load(Ordering::SeqCst){
                                    let broadcast_ts = bead.uncommitted_metadata.broadcast_timestamp.clone().to_u32();
                                    let (ts_tx, ts_rx) = tokio::sync::oneshot::channel();
                                    if let Err(e) = ibd_command_tx
                                        .send(IBDCommands::FetchAllTimestamps { sender: ts_tx })
                                        .await {
                                        tracing::warn!("Failed to request timestamp map: {:?}", e);
                                    }
                                    let timestamp_map = match ts_rx.await {
                                        Ok(map) => map,
                                        Err(_) => {
                                            tracing::error!("Failed to receive timestamp map");
                                            continue;
                                        }
                                    };
                                      //If the received  bead exceeds the timestamp of ibd completion wrt to a sync node
                                      if let braid::AddBeadStatus::ParentsNotYetReceived = status {
                                        //request the parents using request response protocol
                                        let peer_id = peer_manager.get_top_k_peers_for_propagation(1);
                                        if let Some(peer) = peer_id.first() {
                                            swarm.behaviour_mut().bead_sync.send_request(
                                                &peer,
                                                BeadRequest::GetBeads(
                                                    BeadHashes(
                                                        bead.committed_metadata
                                                            .parents
                                                            .clone()
                                                            .into_iter()
                                                            .collect(),
                                                    )
                                                ),
                                            );
                                        } else {
                                            warn!(parent_count = %bead.committed_metadata.parents.len(), "Insufficient peers for bead sync");
                                        }
                                    } else if let braid::AddBeadStatus::InvalidBead = status {
                                        // update the peer manager about the invalid bead
                                        peer_manager.penalize_for_invalid_bead(&message.source);
                                    } else if let braid::AddBeadStatus::BeadAdded = status {
                                     //Considering the index of the beads in braid will be same as the (insertion ids-1)
                                        let bead_id = match braid_data
                                            .bead_index_mapping
                                            .get(&bead.block_header.block_hash()) {
                                            Some(id) => id,
                                            None => {
                                                error!(bead_hash = ?bead.block_header.block_hash(), "Bead ID not found in index mapping");
                                                continue;
                                            }
                                        };
                                        let (txs_json, relative_json, parent_timestamp_json) = match prepare_bead_tuple_data(
                                            &braid_data.beads,
                                            &braid_data.bead_index_mapping,
                                            &bead,
                                        ){
                                            Ok(received_tuples)=>received_tuples,
                                            Err(error)=>{
                                                error!("An error occurred while preparing bead tuple data for bead with beadhash - {:?} due to {:?}",bead.block_header.block_hash(),error);
                                                continue;
                                            }
                                        };
                                        // update score of the peer and adding to local db store
                                        let _query_send_result = match db_tx.send(node::db::BraidpoolDBTypes::InsertTupleTypes { query: node::db::InsertTupleTypes::InsertBeadSequentially { bead_to_insert: bead,txs_json:txs_json,relative_json:relative_json,parent_timestamp_json:parent_timestamp_json,bead_id:*bead_id } }).await{
                                           Ok(_)=>{
                                               debug!("Insert command sent successfully to db handler after receiving bead from peer");
                                           },
                                           Err(error)=>{
                                               error!(
                                                   source = ?message.source,
                                                   err = ?error.0,
                                                   "An error occurred while sending insert bead command received from peer"
                                               );
                                           }
                                        };
                                        peer_manager.update_score(&message.source, 1.0);
                                    }
                                    for (sync_peer, ibd_ts) in timestamp_map.iter() {
                                        let threshold = *ibd_ts + LATENCY_ALPHA * 10;
                                        let sync_peer_id = match sync_peer.parse::<PeerId>() {
                                            Ok(id) => id,
                                            Err(e) => {
                                                error!(sync_peer = %sync_peer, error = %e, "Failed to parse sync peer ID");
                                                continue;
                                            }
                                        };
                                        // broadcast_timestamp < timestamp + alpha * 10
                                        if broadcast_ts  < threshold as u32 {
                                            info!("Incoming BEAD received during IBD within threshold limit with broadcast timestamp - {:?} and threshold is - {:?}",broadcast_ts,threshold);
                                           match status{
                                            braid::AddBeadStatus::InvalidBead | braid::AddBeadStatus::ParentsNotYetReceived=>{
                                                //Aborting/evicting the wait_ibd handler corresponding to the sync peer
                                                match ibd_command_tx.send(IBDCommands::AbortWaitHandle { peer_id:sync_peer_id }).await{
                                                    Ok(_)=>{
                                                        warn!("Abort handle and evicting handler corresponding to sync peer sent successfully");
                                                    },
                                                    Err(error)=>{
                                                        error!(error=?error,"An error occurred while sending abort handler wrt sync peer due to -");
                                                    }
                                                };
                                                // If result is invalid then reinitiate IBD
                                                match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                    Ok(_)=>{
                                                        warn!("Reinitiating IBD command sent to swarm handler");
                                                    },
                                                    Err(error)=>{
                                                        error!(error=?error,"Reinitiating IBD failed in GetAllBeads Response - ");
                                                    }
                                                }
                                                continue;
                                            },
                                            braid::AddBeadStatus::BeadAdded | braid::AddBeadStatus::DagAlreadyContainsBead =>{
                                                ibd_spinlock.store(false,Ordering::SeqCst);
                                                continue;
                                            },
                                           }

                                        }
                                        else{
                                            ibd_spinlock.store(false,Ordering::SeqCst);
                                            continue;
                                        }
                                    }
                                }
                                else{
                                    if let braid::AddBeadStatus::ParentsNotYetReceived = status {
                                        //request the parents using request response protocol
                                        let peer_id = peer_manager.get_top_k_peers_for_propagation(1);
                                        if let Some(peer) = peer_id.first() {
                                            swarm.behaviour_mut().bead_sync.send_request(
                                                &peer,
                                                BeadRequest::GetBeads(
                                                    BeadHashes(
                                                        bead.committed_metadata
                                                            .parents
                                                            .clone()
                                                            .into_iter()
                                                            .collect(),
                                                    )
                                                ),
                                            );
                                        } else {
                                            warn!(parent_count = %bead.committed_metadata.parents.len(), "Insufficient peers for bead sync");
                                        }
                                    } else if let braid::AddBeadStatus::InvalidBead = status {
                                        // update the peer manager about the invalid bead
                                        peer_manager.penalize_for_invalid_bead(&message.source);
                                    } else if let braid::AddBeadStatus::BeadAdded = status {
                                        let bead_id = match braid_data
                                            .bead_index_mapping
                                            .get(&bead.block_header.block_hash()) {
                                            Some(id) => id,
                                            None => {
                                                error!(bead_hash = ?bead.block_header.block_hash(), "Bead ID not found in index mapping (GetAllBeads)");
                                                continue;
                                            }
                                        };
                                        let (txs_json, relative_json, parent_timestamp_json) = match prepare_bead_tuple_data(
                                            &braid_data.beads,
                                            &braid_data.bead_index_mapping,
                                            &bead,
                                        ){
                                            Ok(received_tuples)=>received_tuples,
                                            Err(error)=>{
                                                error!("An error occurred while preparing bead tuple data for bead with beadhash - {:?} due to {:?}",bead.block_header.block_hash(),error);
                                                continue;
                                            }
                                        };
                                        // update score of the peer and adding to local db store
                                        let _query_send_result = match db_tx.send(node::db::BraidpoolDBTypes::InsertTupleTypes { query: node::db::InsertTupleTypes::InsertBeadSequentially { bead_to_insert: bead,txs_json:txs_json,relative_json:relative_json,parent_timestamp_json:parent_timestamp_json,bead_id:*bead_id } }).await{
                                            Ok(_)=>{
                                               debug!("Insert command sent successfully to db handler after receiving bead from peer");
                                           },
                                           Err(error)=>{
                                               error!(
                                                   source = ?message.source,
                                                   err = ?error.0,
                                                   "An error occurred while sending insert bead command received from peer"
                                               );
                                           }
                                        };
                                        peer_manager.update_score(&message.source, 1.0);
                                    }
                                }

                             }
                             Err(e) => {
                                 error!(error = %e, "Failed to deserialize bead");
                             }
                         }
                     }
                     SwarmEvent::NewListenAddr { address, .. } => {
                         info!(address = ?address, "P2P listening on address")
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(
                         identify::Event::Sent { peer_id, .. },
                     )) => {
                         debug!(peer = ?peer_id, "Sent identify info");
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(
                         identify::Event::Received { peer_id, info,  .. },
                     )) => {
                         let info_reference = info.clone();
                         info!(
                             peer = ?peer_id,
                             address_count = %info_reference.listen_addrs.len(),
                             "Received listen addresses"
                         );
                         if info.protocols.iter().any(|p| *p == KADPROTOCOLNAME) {
                             for addr in info.listen_addrs {
                                 info!(address = %addr, "Received address via identify");
                             }
                         } else {
                             info!(peer = ?peer_id, "Peer does not support Kademlia");
                         }
                         if info_reference
                             .clone()
                             .protocols
                             .iter()
                             .any(|p| *p != BEAD_ANNOUNCE_PROTOCOL)
                         {

                             info!(
                                 peer_address = ?info_reference.observed_addr,
                                 "Peer does not support floodsub"
                             );
                         }
                         debug!(info = ?info_reference, "Received peer info");
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Kademlia(
                         kad::Event::OutboundQueryProgressed { result, .. },
                     )) => match result {
                         QueryResult::GetClosestPeers(Ok(ok)) => {
                             info!(peers = ?ok.peers, peer_count = %ok.peers.len(), "Got closest peers");
                         }
                         QueryResult::GetClosestPeers(Err(err)) => {
                             error!(error = %err, "Failed to get closest peers");
                         }
                        QueryResult::Bootstrap(Ok(BootstrapOk {
                            peer, ..
                        }))=>{
                            info!(peer = ?peer, "New peer");
                        }
                         _ => info!(result = ?result, "Other DHT query result"),
                     },
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(
                         identify::Event::Error {
                             peer_id,
                             error,
                             connection_id: _,
                         },
                     )) => {
                         error!(peer = %peer_id, error = ?error, "Identify event error");
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Ping(ping::Event {
                         peer,
                         result,
                         ..
                     })) => {
                         match result {
                             Ok(latency) => {
                                 info!(
                                     peer = %peer,
                                     latency_ms = %latency.as_millis(),
                                     "Ping"
                                 );
                                peer_manager.update_latency(&peer,latency);
                             }
                             Err(err) => {
                                 warn!(
                                     peer = %peer,
                                     error = %err,
                                     "Ping failed"
                                 );
                             }
                         }
                     }
                     SwarmEvent::ConnectionEstablished {
                         peer_id, endpoint, ..
                     } => {

                         // Add the peer to the peer manager
                         let remote_addr = endpoint.get_remote_address();
                         swarm.behaviour_mut().kademlia.add_address(&peer_id,remote_addr.clone());
                         info!(address = ?remote_addr, "DHT updated with peer address");
                         swarm.behaviour_mut()
                         .bead_announce
                         .add_node_to_partial_view(peer_id);

                         info!(peer = %peer_id, "Peer added to floodsub mesh");
                         let ip = remote_addr.iter().find_map(|p| match p {
                             libp2p::core::multiaddr::Protocol::Ip4(ip) => {
                                 Some(std::net::IpAddr::V4(ip))
                             }
                             libp2p::core::multiaddr::Protocol::Ip6(ip) => {
                                 Some(std::net::IpAddr::V6(ip))
                             }
                             _ => None,
                         });
                         peer_manager.add_peer(peer_id, !endpoint.is_dialer(), ip);
                         info!(
                            peer_id = ?peer_id,
                            remote_addr = ?remote_addr,
                            "Connection established to peer"
                        );

                     }
                     SwarmEvent::ConnectionClosed {
                         peer_id,
                         connection_id,
                         endpoint,
                         num_established,
                         cause,
                     } => {
                         info!(peer = %peer_id, connection_id = %connection_id, address = %endpoint.get_remote_address(), established = %num_established, cause = ?cause, "Connection closed");
                         // Remove the peer from the peer manager
                         peer_manager.remove_peer(&peer_id);
                         swarm
                             .behaviour_mut()
                             .kademlia
                             .remove_address(&peer_id, endpoint.get_remote_address());
                     }
                     SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadSync(
                    request_response::Event::Message {
                        peer,
                        message,
                        connection_id,
                    },
                )) => {
                    info!(
                        peer = %peer,
                        message = ?message,
                        connection = ?connection_id,
                        "Bead sync message received"
                    );
                    match message {
                        request_response::Message::Request {
                            request,
                            request_id: _,
                            channel,
                        } => {
                            // Handle the bead sync request here
                            match request {
                                BeadRequest::GetBeads(hashes) => {
                                        let mut beads = Vec::new();
                                        {
                                            let braid_lock = braid.read().await;
                                            for hash in hashes.iter() {
                                                if let Some(index) =
                                                    braid_lock.bead_index_mapping.get(hash)
                                                {
                                                    if let Some(bead) = braid_lock.beads.get(*index) {
                                                        beads.push(bead.clone());
                                                    }
                                                }
                                            }
                                        }
                                        //Sending all the beads requested in the hashes supplied during `GetData` request
                                        swarm.behaviour_mut().respond_with_beads(channel, beads);
                                }
                                BeadRequest::GetTips => {
                                        let tips;
                                        {
                                            let braid_lock = braid.read().await;
                                            tips = braid_lock
                                                .tips
                                                .iter()
                                                .filter_map(|index| braid_lock.beads.get(*index))
                                                .cloned()
                                                .map(|bead| bead.block_header.block_hash())
                                                .collect();
                                        }
                                        swarm.behaviour_mut().respond_with_tips(channel, tips);
                                }
                                BeadRequest::GetGenesis => {
                                        let genesis;
                                        {
                                            let braid_lock = braid.read().await;
                                            genesis = braid_lock
                                                .genesis_beads
                                                .iter()
                                                .filter_map(|index| braid_lock.beads.get(*index))
                                                .cloned()
                                                .map(|bead| bead.block_header.block_hash())
                                                .collect();
                                        }
                                        swarm.behaviour_mut().respond_with_genesis(channel, genesis);
                                }
                                BeadRequest::GetAllBeads => {

                                        let all_beads;
                                        {
                                            let braid_lock = braid.read().await;
                                            all_beads = braid_lock.beads.iter().cloned().collect();
                                        }
                                        swarm.behaviour_mut().respond_with_beads(channel, all_beads);
                                }
                                BeadRequest::GetBeadsAfter(hashes) => {
                                        let beads = braid.read().await.get_beads_after(hashes.into());
                                        if let Some(response_beads) = beads {
                                            let mut computed_beads_hashes:Vec<BeadHash> = Vec::new();
                                            for bead in response_beads.into_iter(){
                                                computed_beads_hashes.push(bead.block_header.block_hash());
                                            }
                                            //Sending the corresponding bead hashes requested by the new peer for IBD that will
                                            //be after the new peer's `Tips`.
                                            swarm
                                                .behaviour_mut()
                                                .respond_with_beadhashes(channel, computed_beads_hashes);
                                        } else {
                                            swarm.behaviour_mut().respond_with_error(
                                                channel,
                                                BeadSyncError::BeadHashNotFound,
                                            );
                                        }
                                }
                            }
                        }
                        request_response::Message::Response {
                            request_id: _,
                            response,
                        } => {
                            match response {
                                BeadResponse::Beads(beads)
                                | BeadResponse::GetAllBeads(beads) => {
                                    let (beads_tx, beads_rx) = tokio::sync::oneshot::channel::<Vec<BeadHash>>();
                                    //Fetching the pruned bead-hashes received during `GetBeadAfter` request
                                    match ibd_command_tx.send(IBDCommands::FetchGetBeadMapping { peer_id: peer.to_string(), beadhash_sender: beads_tx }).await{
                                        Ok(_)=>{
                                            debug!("IBD command sent to handler successfully !");
                                        },
                                        Err(error)=>{
                                            //Re-initiating IBD
                                            error!("An error occurred while sending ibd command to ibd_handler - {:?}, re-trying IBD",error.0);
                                            match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                Ok(_)=>{
                                                    warn!("Reinitiating IBD command sent to swarm handler");
                                                },
                                                Err(error)=>{
                                                    error!(error=?error,"Reinitiating IBD failed in GetAllBeads Response - ");
                                                }
                                            }
                                            continue;
                                        }
                                    };
                                    let pruned_beads = match beads_rx.await{
                                        Ok(received_beads)=>{
                                            received_beads
                                        },
                                        Err(error)=>{
                                            error!(error=?error.to_string(),"An error occurred while receiving cached beads from ibd_handler due to , re-trying IBD");
                                            match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                Ok(_)=>{
                                                    warn!("Reinitiating IBD command sent to swarm handler");
                                                },
                                                Err(error)=>{
                                                    error!(error=?error,"Reinitiating IBD failed in GetAllBeads Response - ");
                                                }
                                            }
                                            continue;
                                        }
                                    };
                                    for bead in beads.into_iter() {
                                        let mut braid_data = braid.write().await;
                                        let status = braid_data.extend(&bead);
                                        let curr_beadhash = bead.block_header.block_hash().to_string();
                                        if let braid::AddBeadStatus::InvalidBead = status {
                                            // update the peer manager about the invalid bead
                                            peer_manager.penalize_for_invalid_bead(&peer);
                                        } else if let braid::AddBeadStatus::BeadAdded = status {
                                            let bead_id = match braid_data
                                                .bead_index_mapping
                                                .get(&bead.block_header.block_hash()) {
                                                Some(id) => id,
                                                None => {
                                                    error!(bead_hash = ?bead.block_header.block_hash(), "Bead ID not found in index mapping (GetBeadsAfter)");
                                                    continue;
                                                }
                                            };
                                            let (txs_json, relative_json, parent_timestamp_json) = match prepare_bead_tuple_data(
                                                &braid_data.beads,
                                                &braid_data.bead_index_mapping,
                                                &bead,
                                            ){
                                                Ok(received_tuples)=>received_tuples,
                                                Err(error)=>{
                                                    error!("An error occurred while preparing bead tuple data for bead with beadhash - {:?} due to {:?}",curr_beadhash,error);
                                                    continue;
                                                }
                                            };
                                            // update score of the peer
                                            peer_manager.update_score(&peer, 1.0);
                                            //persisting the received beads from peer onto DB(disk)
                                            match db_tx.send(node::db::BraidpoolDBTypes::InsertTupleTypes { query: node::db::InsertTupleTypes::InsertBeadSequentially { bead_to_insert: bead,txs_json:txs_json,parent_timestamp_json:parent_timestamp_json,relative_json:relative_json,bead_id:*bead_id } }).await{
                                                Ok(_)=>{
                                                    debug!(beadhash=?curr_beadhash,"Bead received in IBD persisted over disk with beadhash and status BeadAdded");
                                                },
                                                Err(error)=>{
                                                    tracing::error!(
                                                        peer = %peer,
                                                        err = ?error.0,
                                                        "An error occurred while persisting received bead from peer"
                                                    );
                                                }
                                            };
                                        }
                                    }
                                    //Preparing next batch request to be sent to the sync node
                                    let (batch_tx, batch_rx) = tokio::sync::oneshot::channel::<usize>();
                                    match ibd_command_tx.send(IBDCommands::UpdateAndFetchBatchOffset { peer_id: peer.to_string(), offset_sender: batch_tx, batch_size:IBD_BATCH_SIZE  }).await{
                                            Ok(_)=>{
                                                debug!("Offset Updated");
                                            },
                                            Err(error)=>{
                                                error!(error=?error,"An error occurred while sending the offset update command, re-trying IBD");
                                                match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                    Ok(_)=>{
                                                        warn!("Reinitiating IBD command sent to swarm handler");
                                                    },
                                                    Err(error)=>{
                                                        error!(error=?error,"Reinitiating IBD failed in GetAllBeads Response - ");
                                                    }
                                                }
                                                continue;
                                            }
                                    };
                                    let next_batch_offset = match batch_rx.await{
                                        Ok(next_offset)=>{
                                            debug!(next_offset=?next_offset,"Newer offset for batch request received successfully ");
                                            next_offset
                                        },
                                        Err(error)=>{
                                            error!(error=?error,"An error occurred while receiving the offset, re-trying IBD");
                                            match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                Ok(_)=>{
                                                    warn!("Reinitiating IBD command sent to swarm handler");
                                                },
                                                Err(error)=>{
                                                    error!(error=?error,"Reinitiating IBD failed in GetAllBeads Response - ");
                                                }
                                            }
                                            continue;
                                        }
                                    };
                                    if next_batch_offset < pruned_beads.len() && ((next_batch_offset+IBD_BATCH_SIZE)< pruned_beads.len()){
                                        info!("Received beads within batch range");
                                        swarm.behaviour_mut().request_beads(peer, &pruned_beads[next_batch_offset..(next_batch_offset+IBD_BATCH_SIZE)].to_vec());
                                    }
                                    else if next_batch_offset < pruned_beads.len() && ((next_batch_offset+IBD_BATCH_SIZE)>=pruned_beads.len()){
                                        info!("Received beads within batch range");
                                        swarm.behaviour_mut().request_beads(peer, &pruned_beads[next_batch_offset..].to_vec());

                                    }
                                    else{
                                        //IBD completed
                                        info!(
                                            peer = %peer,
                                            "Initial IBD has been completed with respect to peer"
                                        );
                                        // Get current time and create recent timestamps (within last hour)
                                        let current_time = SystemTime::now()
                                            .duration_since(UNIX_EPOCH)
                                            .map(|d| d.as_secs())
                                            .unwrap_or_else(|e| {
                                                error!(error = %e, "System time before UNIX epoch");
                                                0
                                            });
                                        match ibd_command_tx.send(IBDCommands::UpdateTimestampMapping { peer_id: peer.to_string(), end_timestamp: current_time }).await{
                                            Ok(_)=>{
                                                debug!("Timestamp updated command sent successfully");
                                                //Scheduling a corresponding watcher task that will check after a latency period
                                                //if no incoming is received during the instance of [initial_headers_fetched,(initial_headers_fetched+(alpha*10))]
                                                let ibd_spinlock_ref = ibd_spinlock.clone();
                                                let ibd_incoming_handler = tokio::spawn(async move{
                                                    //Sleeping for a fixed duration to be set according to statistical estimates
                                                    tokio::time::sleep(Duration::from_secs(MAX_IBD_INCOMING_THRESHOLD)).await;
                                                    //We will check if no bead is `incoming` after the duration of 600 seconds then we will reset/set ibd_flag accordingly
                                                    if ibd_spinlock_ref.load(Ordering::SeqCst){
                                                        //If no incoming is received during the period then we can say
                                                        //that ibd wrt the given sync node is successfully completed
                                                        ibd_spinlock_ref.store(false,Ordering::SeqCst);
                                                        warn!("Maximum threshold wrt IBD incoming exceeded thus ibd_flag being set to false");
                                                    }

                                                });
                                                //At retry we will have to abort and evict the corresponding sync-peers's wait handle
                                                match ibd_command_tx.send(IBDCommands::UpdateIncomingBeadMapping{peer_id:peer,retry_or_not:false,handle:Some(ibd_incoming_handler)}).await{
                                                    Ok(_)=>{
                                                        debug!("Incoming bead command sent successfully");
                                                    },
                                                    Err(error)=>{
                                                        error!(error=?error,"An error occurred while sending Update Incoming due to ");
                                                    }
                                                };
                                            },
                                            Err(error)=>{
                                                error!(error=?error,"An error occurred while sending timestamp update command for the given sync node");
                                            }
                                        };
                                    }
                                }
                                 BeadResponse::GetBeadsAfter(bead_hashes)=>{
                                    //Getting all the beadhashes after the common oldest in both the peers
                                    let (tips_tx, tips_rx) = tokio::sync::oneshot::channel::<Vec<BeadHash>>();
                                    match ibd_command_tx.send(IBDCommands::FetchTips { peer_id: peer.to_string(), tips_sender: tips_tx }).await{
                                        Ok(_)=>{
                                            debug!("Sync peer Tips received successfully.");
                                        },
                                        Err(error)=>{
                                            error!(error=?error,"Error occurred while receiving tips, re-trying IBD");
                                            match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                Ok(_)=>{
                                                    warn!("Reinitiating IBD command sent to swarm handler");
                                                },
                                                Err(error)=>{
                                                    error!(error=?error,"Reinitiating IBD failed in GetBeadsAfter Response - ");
                                                }
                                            }
                                            continue;
                                        }
                                    };
                                    let received_tips = match tips_rx.await{
                                        Ok(received_tips)=>{
                                            received_tips
                                        },
                                        Err(error)=>{
                                            error!(error=?error,"An error occurred while receiving the Tips, re-trying IBD");
                                            match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                Ok(_)=>{
                                                    warn!("Reinitiating IBD command sent to swarm handler");
                                                },
                                                Err(error)=>{
                                                    error!(error=?error,"Reinitiating IBD failed in GetBeadsAfter Response - ");
                                                }
                                            }
                                            continue;
                                        }
                                    };
                                    //Pruning the hashes wrt cached `Tips`
                                    let mut found_tips = HashSet::new();
                                    let mut pruned = Vec::new();
                                    let tips_set: HashSet<_> = received_tips.into_iter().collect();
                                    for hash in bead_hashes {
                                        if tips_set.contains(&hash) {
                                            found_tips.insert(hash.clone());
                                        }
                                        pruned.push(hash);
                                        // Stop once all tips have been matched
                                        if found_tips.len() == tips_set.len() {
                                            break;
                                        }
                                    }
                                    let pruned_ref = pruned.clone();
                                    // Storing them in cache
                                    match ibd_command_tx.send(IBDCommands::UpdateIncoming { get_bead_response: pruned, peer_id: peer.to_string() }).await{
                                        Ok(_)=>{
                                            debug!("Received beads to be fetched in GetBeads saved successfully");
                                        },
                                        Err(error)=>{
                                            error!(error=?error,"An error occurred while Caching pruned beadhashes to be fetched in GetBeads");
                                            match swarm_command_sender.send(SwarmCommand::InitiateIBD).await{
                                                Ok(_)=>{
                                                    warn!("Reinitiating IBD command sent to swarm handler");
                                                },
                                                Err(error)=>{
                                                    error!(error=?error,"Reinitiating IBD failed in GetBeadsAfter Response - ");
                                                }
                                            }
                                            continue;
                                        }
                                    };
                                    // Initiating `GetBead` request cycle
                                    if pruned_ref.len() <= IBD_BATCH_SIZE{
                                        swarm.behaviour_mut().request_beads(peer, &pruned_ref);
                                    }
                                    else{
                                        swarm.behaviour_mut().request_beads(peer, &pruned_ref[0..IBD_BATCH_SIZE].to_vec());
                                    }

                                }
                                BeadResponse::Tips(tips) => {
                                    info!(tips = ?tips, tip_count = %tips.len(), "Received braid tips");
                                    //If received tips are already present in the local braid arc then we can stop
                                    //IBD and continue with mining
                                    //Initializing the batch offset for the corresponding sync peer
                                    let (ibd_bridge_tx, _ibd_bridge_rx) = tokio::sync::oneshot::channel::<usize>();
                                    match ibd_command_tx.send(IBDCommands::UpdateAndFetchBatchOffset { peer_id: peer.to_string(), offset_sender: ibd_bridge_tx, batch_size: IBD_BATCH_SIZE }).await{
                                        Ok(_)=>{
                                            debug!("Offset Initialized successfully");
                                        },
                                        Err(_error)=>{
                                            error!("An error occurred while sending offset initalization command to ibd_handler");
                                            continue;
                                        }
                                    };
                                    let _val = match _ibd_bridge_rx.await {
                                        Ok(v) => v,
                                        Err(e) => {
                                            error!(error = %e, "Failed to receive IBD batch offset");
                                            continue;
                                        }
                                    };
                                    let braid_data = braid.read().await;

                                    let bead_hash_set: HashSet<BeadHash> = braid_data
                                    .beads
                                    .iter()
                                    .map(|b| b.block_header.block_hash())
                                    .collect();

                                    let flag = tips.iter().all(|tip_hash| bead_hash_set.contains(tip_hash));

                                    if flag{
                                        //No need to proceed further and continue to next event
                                        info!("Peer already synced to tip");
                                        //IBD flag can be set  as the current bead is already synced//
                                        ibd_spinlock.store(false, Ordering::SeqCst);
                                        continue;
                                    }
                                  let _update_tip_cache_ack = match  ibd_command_tx.send(IBDCommands::UpdateIBDTipsMapping { received_tips: tips.0, peer_id: peer.to_string() }).await{
                                    Ok(_)=>{
                                        debug!("Sync peers Tip mapping update successfully");
                                    },
                                    Err(error)=>{
                                        tracing::error!(
                                            err = ?error,
                                            "Error while sending update cache command"
                                        );
                                        continue;
                                    }
                                  };
                                    // After storing tips we will issue `GetBeads` command that will find the oldest
                                    // common bead if any and will send the beadhashes of all the next beads this will either be the current tips or
                                    // the current genesis in all the cases in case of new braid-node this will be genesis otherwise it will always be tips
                                    let mut current_tip_hashes = Vec::new();
                                    for curr_bead_idx in braid_data.tips.iter() {
                                        if let Some(current_bead) = braid_data.beads.get(*curr_bead_idx) {
                                            current_tip_hashes.push(current_bead.block_header.block_hash());
                                        } else {
                                            error!(bead_idx = %curr_bead_idx, "Tip bead not found in beads list");
                                        }
                                    }
                                    // Sending the current bead hashes for the receiving of beads to start in batches
                                    let get_bead_start_request:BeadRequest = BeadRequest::GetBeadsAfter(BeadHashes(current_tip_hashes));
                                    swarm.behaviour_mut().bead_sync.send_request(&peer,get_bead_start_request);

                                }
                                BeadResponse::Genesis(genesis) => {
                                    info!(genesis=?genesis,"Received genesis beads: ");
                                    let status = {
                                        let braid_lock = braid.read().await;
                                        braid_lock.check_genesis_beads(&genesis.0)
                                    };
                                    match status {
                                        braid::GenesisCheckStatus::GenesisBeadsValid => {
                                            info!("Genesis beads are valid");
                                        }
                                        braid::GenesisCheckStatus::MissingGenesisBead => {
                                            warn!(peer = %peer, "Missing genesis bead");
                                            swarm
                                                .behaviour_mut()
                                                .request_beads(peer, &genesis.0);
                                        }
                                        braid::GenesisCheckStatus::GenesisBeadsCountMismatch => {
                                            warn!(
                                                received = %genesis.0.len(),
                                                peer = %peer,
                                                "Genesis bead count mismatch"
                                            );
                                        }
                                    }
                                }
                                BeadResponse::Error(error) => match error {
                                    BeadSyncError::GenesisMismatch => {
                                        warn!("Genesis mismatch error received");
                                        swarm.behaviour_mut().request_genesis(peer.clone());
                                    }
                                    BeadSyncError::BeadHashNotFound => {
                                        warn!("Peer requested bead hashes not found in local store");
                                    }
                                },
                            };
                        }
                    }
                }
                     other_event=>{
                             debug!(event = ?other_event, "Other swarm event");
                     }
                 }

             }
             Some(swarm_command) = swarm_command_receiver.recv()=>{
                 match swarm_command{
                     SwarmCommand::PropagateValidBead {
                         bead_bytes,
                     } => {
                         swarm
                             .behaviour_mut()
                             .bead_announce
                             .publish(current_broadcast_topic.clone(), bead_bytes);
                        info!(topic = ?current_broadcast_topic, "Published bead to floodsub topic");
                     },
                     SwarmCommand::InitiateIBD=>{
                        info!("Initiating IBD after peer discovery and selecting peer with lowest latency score");
                        //Evicting lowest latency peer id
                        let peer_ids = peer_manager.get_top_k_peers_for_propagation(1);
                        if peer_ids.len() == 0 {
                            warn!("No peer available for syncing to take place");
                                tokio::spawn({
                                    let swarm_command_sender = swarm_command_sender.clone();
                                    //Retrying at fixed interval in case of no sync peers being available
                                    async move {
                                        tokio::time::sleep(Duration::from_secs(IBD_TRIGGER_AFTER)).await;
                                        match swarm_command_sender.send(SwarmCommand::InitiateIBD).await {
                                            Ok(_) => {
                                                info!("Retrying IBD when no sync peers are available");
                                            }
                                            Err(error) => {
                                                error!(error=?error, "Failed to reinitiate IBD when no sync peer was available");
                                            }
                                        }
                                    }
                                });
                        }
                        else{
                            let mut sync_request_sent = false;
                            for lowest_latency_peer in peer_ids.into_iter(){
                                let (retry_count_tx,retry_count_rx) = tokio::sync::oneshot::channel();
                                match ibd_command_tx.send(IBDCommands::GetIncomingBeadRetryCount{peer_id:lowest_latency_peer,retry_sender:retry_count_tx}).await{
                                    Ok(_)=>{
                                        info!(peer=?lowest_latency_peer,"Retry count corresponding to peer received successfully");
                                    },
                                    Err(error)=>{
                                        error!(error=?error,"An error occurred while sending retry count to IBDHandler");
                                    }
                                }
                                let retry_cnt = match retry_count_rx.await {
                                    Ok(cnt) => cnt,
                                    Err(e) => {
                                        error!(error=?e, "Failed to receive retry count from IBDHandler, channel closed or sender dropped");
                                        continue;
                                    }
                                };
                                if retry_cnt >= MAX_IBD_RETRIES && retry_cnt != u64::MAX{
                                    warn!("Corresponding peer {:?} retries for IBD exceeded selecting next lowest latent peer",lowest_latency_peer);
                                    continue;
                                }
                                else if retry_cnt == u64::MAX{
                                    //First time syncing is being done wrt the provided peer
                                    match ibd_command_tx.send(IBDCommands::UpdateIncomingBeadMapping{peer_id:lowest_latency_peer,retry_or_not:false,handle:None}).await{
                                        Ok(_)=>{
                                            info!("Incoming bead command sent successfully");
                                            let sync_start_request:BeadRequest = BeadRequest::GetTips;
                                            swarm.behaviour_mut().bead_sync.send_request(&lowest_latency_peer, sync_start_request);
                                        },
                                        Err(error)=>{
                                            error!(error=?error,"An error occurred while sending Update Incoming due to ");
                                        }
                                    };
                                    sync_request_sent = true;
                                    break;
                                }
                                else{
                                    //Case of retry is there
                                    match ibd_command_tx.send(IBDCommands::UpdateIncomingBeadMapping{peer_id:lowest_latency_peer,retry_or_not:true,handle:None}).await{
                                        Ok(_)=>{
                                            info!("Incoming bead command sent successfully");
                                        },
                                        Err(error)=>{
                                            error!(error=?error,"An error occurred while sending Update Incoming due to ");
                                        }
                                    };
                                    //Initiating IBD and sending the request to fetch tips and store them in a centralized mapping owned by main_thread .
                                    let sync_start_request:BeadRequest = BeadRequest::GetTips;
                                    swarm.behaviour_mut().bead_sync.send_request(&lowest_latency_peer, sync_start_request);
                                    sync_request_sent = true;
                                    break;
                                }

                            }
                            if sync_request_sent{
                                //The lowest latency avaialble sync peer whose retry count is not exceeded has been selected and requested to initiate IBD
                                continue;
                            }
                            else{
                                warn!("Retry count for all the available sync peers exceeded waiting for new peer connections");
                                tokio::spawn({
                                    let swarm_command_sender = swarm_command_sender.clone();
                                    //Retrying at fixed interval in case of all available sync peer retry count has exceeded
                                    //Probe at fixed interval for any new peer
                                    async move {
                                        tokio::time::sleep(Duration::from_secs(IBD_TRIGGER_AFTER)).await;
                                        match swarm_command_sender.send(SwarmCommand::InitiateIBD).await {
                                            Ok(_) => {
                                                info!("Retrying IBD when no sync peers are available");
                                            }
                                            Err(error) => {
                                                error!(error=?error, "Failed to reinitiate IBD when no sync peer was available");
                                            }
                                        }
                                    }
                                });
                            }
                        }
                     }
                 }
             }




            }
        }
    });

    //graceful shutdown via `Cancellation token`
    let shutdown_signal = tokio::signal::ctrl_c().await;
    match shutdown_signal {
        Ok(_) => {
            info!(component = "database", "Closing connection pool");
            let pool = db_connection_pool.lock().await;
            //Closing all the existing connections to pool and committing from .db-wal to .db
            pool.close().await;
            info!(component = "database", "Connections closed");
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
