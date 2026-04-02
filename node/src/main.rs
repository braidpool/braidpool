use bitcoin::{
    consensus::encode::deserialize, ecdsa::Signature, pow::CompactTargetExt, BlockHash,
    CompactTarget, EcdsaSighashType, Network, Txid,
};
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
use node::committed_metadata::{CommittedMetadata, TimeVec, TxIdVec};
use node::db::db_handlers::fetch_beads_in_batch;
use node::utils::BeadHash;
use node::SwarmHandler;
use node::{
    bead::{Bead, BeadHashes, BeadRequest, BeadResponse, BeadSyncError},
    behaviour::{self, BEAD_ANNOUNCE_PROTOCOL, BRAIDPOOL_TOPIC},
    braid,
    braid::AddBeadStatus,
    cli,
    db::db_handlers::DBHandler,
    ipc_template_consumer,
    peer_manager::PeerManager,
    peer_manager::{IBD_BATCH_SIZE, IBD_RETRY_DELAY, MAX_IBD_RETRIES, MIN_PEERS_FOR_IBD},
    rpc_server::{run_rpc_server, BitcoinRpcConfig, RpcProxyCommand},
    setup_tracing,
    stratum::{BlockTemplate, ConnectionMapping, Notifier, NotifyCmd, Server, StratumServerConfig},
    uncommitted_metadata::UnCommittedMetadata,
    SwarmCommand, TemplateId,
};
use num::ToPrimitive;
use std::collections::HashSet;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::str::FromStr;
use std::sync::Arc;
use std::time::UNIX_EPOCH;
use std::{collections::HashMap, error::Error};
use std::{fs, time::Duration};
use tokio_util::sync::CancellationToken;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

use behaviour::{BraidPoolBehaviour, BraidPoolBehaviourEvent};

use crate::behaviour::KADPROTOCOLNAME;
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
    //Initializing DB and db command handler
    let (mut _db_handler, db_tx) = DBHandler::new().await.map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Database initialization failed: {:?}", e),
        )
    })?;
    // Initializing the braid object with read write lock
    //for supporting concurrent readers and single writer
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(Vec::from([]))));
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
            info!(
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
    let (swarm_handler, mut swarm_command_receiver) = SwarmHandler::new(db_tx.clone());
    //Swarm command sender
    let swarm_command_sender = swarm_handler.command_sender.clone();
    let swarm_handler_arc = Arc::new(Mutex::new(swarm_handler));
    //cloning the channel to be sent across different interfaces
    let notification_tx_clone = notification_tx.clone();
    //Connection mapping for all the downstream connection connected to the stratum server
    let connection_mapping = Arc::new(tokio::sync::RwLock::new(ConnectionMapping::new()));
    // Clone connection_mapping for RPC server before it's used in async move blocks
    let connection_mapping_for_rpc = Arc::clone(&connection_mapping);
    //Mining job map keeping all the jobs provided to the downstream
    let mining_job_map = Arc::new(Mutex::new(HashMap::new()));
    //Intializing `notifier` for mining.notify
    let mut notifier: Notifier = Notifier::new(notification_rx, Arc::clone(&mining_job_map));
    //Stratum configuration initialization
    let stratum_config: StratumServerConfig = StratumServerConfig::default();
    let (block_submission_tx, block_submission_rx) =
        tokio::sync::mpsc::unbounded_channel::<node::stratum::BlockSubmissionRequest>();

    // IBD will be triggered when peer count threshold is reached
    let mut ibd_initiated = false;

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
    tokio::spawn(async move {
        let _res = stratum_server
            .run_stratum_service(
                mining_job_map,
                notification_tx_clone,
                swarm_handler_arc.clone(),
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
    let peer_manager_arc_for_swarm = peer_manager_arc.clone();
    let swarm_handle = tokio::spawn(async move {
        let braid = std::sync::Arc::clone(&braid);
        let peer_manager_arc = peer_manager_arc_for_swarm;
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
                                debug!(bead = ?bead, hash = %bead.block_header.block_hash(), "Received bead");
                                // Handle the received bead here
                                let mut braid_data = braid.write().await;
                                let status = {
                                    braid_data.extend(&bead)
                                };
                                let bead_mapping_ref = braid_data.bead_index_mapping.clone();
                                if let braid::AddBeadStatus::ParentsNotYetReceived = status {
                                    // There is no need to rqeuest parents immediately they will be solved upon bead received as per the
                                    // latency of mesh and the self mined beads and their propagation via `extend` functionality
                                    warn!("Received bead with missing parents - requesting parents");
                                } else if let braid::AddBeadStatus::InvalidBead = status {
                                    // update the peer manager about the invalid bead
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
                                        peer_manager.penalize_for_invalid_bead(&message.source);
                                    }
                                } else if let braid::AddBeadStatus::BeadAdded = status {
                                    //If the current bead's extension has further led to removal of orphan beads then
                                    //We can get the orphan beads that we can persist in DB also
                                    let bead_id = match braid_data
                                        .bead_index_mapping
                                        .get(&bead.block_header.block_hash()) {
                                        Some(id) => id.0,
                                        None => {
                                            error!(bead_hash = ?bead.block_header.block_hash(), "Bead ID not found in index mapping");
                                            continue;
                                        }
                                    };
                                    let mut removed_orphans: Vec<Bead> = Vec::new();
                                    if bead_id + 1 < braid_data.beads.len() {
                                        warn!("Orphan beads removed from the orphan set upon extension of current bead");
                                        removed_orphans = braid_data.beads[bead_id + 1..].iter().cloned().collect();
                                    } else {
                                        debug!("No orphan beads to remove upon extension of current bead");
                                    }
                                    // update score of the peer and adding to local db store
                                    let _query_send_result = match db_tx.send(node::db::BraidpoolDBTypes::InsertTupleTypes { query: node::db::InsertTupleTypes::InsertBeadSequentially { bead_to_insert: bead,removed_orphans:removed_orphans,bead_index_mapping:bead_mapping_ref,bead_id:bead_id} }).await{
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
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
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
                                {
                                    let mut peer_manager = peer_manager_arc.write().await;
                                    peer_manager.update_latency(&peer,latency);
                                }
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
                         {
                             let mut peer_manager = peer_manager_arc.write().await;
                             peer_manager.add_peer(peer_id, !endpoint.is_dialer(), ip);
                         }
                         info!(
                            peer_id = ?peer_id,
                            remote_addr = ?remote_addr,
                            "Connection established to peer"
                        );
                        // Trigger IBD when peer count threshold is reached
                        {
                            let  peer_manager = peer_manager_arc.write().await;
                            if !ibd_initiated && peer_manager.num_connected_peers() >= MIN_PEERS_FOR_IBD {
                             info!(
                                 peer_count = peer_manager.num_connected_peers(),
                                 threshold = MIN_PEERS_FOR_IBD,
                                 "Peer threshold reached, initiating IBD"
                             );
                             match swarm_command_sender.send(SwarmCommand::InitiateIBD).await {
                                 Ok(_) => {
                                     ibd_initiated = true;
                                     info!("IBD trigger sent based on peer count");
                                 }
                                 Err(error) => {
                                     error!(error=?error, "Failed to send IBD initiation command");
                                 }
                             }
                         }
                        }
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
                         {
                             let mut peer_manager = peer_manager_arc.write().await;
                             peer_manager.remove_peer(&peer_id);
                         }
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
                    debug!(
                        peer = %peer,
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
                                                    if let Some(bead) = braid_lock.beads.get(index.0) {
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
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
                                        peer_manager.handle_fetch_ibd_bead_queue(peer, beads_tx);
                                    }
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

                                    // Collect orphans for batch insertion
                                    let mut all_removed_orphans = Vec::new();
                                    let mut bead_index_mapping = HashMap::new();

                                    for bead in beads.iter() {
                                        let mut braid_data = braid.write().await;
                                        let status = braid_data.extend(&bead);
                                        let curr_beadhash = bead.block_header.block_hash();

                                        if let braid::AddBeadStatus::InvalidBead = status {
                                            // update the peer manager about the invalid bead
                                            {
                                                let mut peer_manager = peer_manager_arc.write().await;
                                                peer_manager.penalize_for_invalid_bead(&peer);
                                            }
                                        } else if let braid::AddBeadStatus::BeadAdded = status {
                                            // Update bead index mapping for batch insert
                                            bead_index_mapping = braid_data.bead_index_mapping.clone();

                                            //If the current bead's extension has further led to removal of orphan beads then
                                            //we can get the orphan beads that we can persist in DB also
                                            let bead_id = bead_index_mapping
                                                .get(&curr_beadhash)
                                                .unwrap()
                                                .0;

                                            if bead_id + 1 < braid_data.beads.len() {
                                                debug!("Orphan beads removed from the orphan set upon extension of current bead");
                                                let removed_orphans: Vec<Bead> = braid_data.beads[bead_id + 1..].iter().cloned().collect();
                                                all_removed_orphans.extend(removed_orphans);
                                            }

                                            // Update score of the peer
                                            {
                                                let mut peer_manager = peer_manager_arc.write().await;
                                                peer_manager.update_score(&peer, 1.0);
                                            }

                                            debug!(beadhash = %curr_beadhash, "Bead added to batch for insertion");
                                        }
                                    }

                                    // Perform batch insertion for all successfully added beads
                                    if !beads.to_vec().is_empty() {
                                        match db_tx.send(node::db::BraidpoolDBTypes::InsertTupleTypes {
                                            query: node::db::InsertTupleTypes::InsertBeadsBatch {
                                                beads_to_insert:beads.to_vec(),
                                                removed_orphans: all_removed_orphans,
                                                bead_index_mapping: bead_index_mapping,
                                            }
                                        }).await {
                                            Ok(_) => {
                                                info!(
                                                    bead_count = beads.len(),
                                                    "Batch insert queued for IBD beads"
                                                );
                                            },
                                            Err(error) => {
                                                error!(
                                                    peer = %peer,
                                                    err = ?error.0,
                                                    "An error occurred while sending batch insert command for IBD beads"
                                                );
                                            }
                                        }
                                    }
                                    //Preparing next batch request to be sent to the sync node
                                    let (batch_tx, batch_rx) = tokio::sync::oneshot::channel::<usize>();
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
                                        peer_manager.handle_update_and_fetch_batch_offset(peer, batch_tx,IBD_BATCH_SIZE);
                                    }
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
                                        let batch_start = next_batch_offset - IBD_BATCH_SIZE;
                                        let batch_num = next_batch_offset / IBD_BATCH_SIZE;
                                        let total_batches = (pruned_beads.len() + IBD_BATCH_SIZE - 1) / IBD_BATCH_SIZE;
                                        info!(
                                            batch = %batch_num,
                                            total = %total_batches,
                                            range = %format!("{}..{}", batch_start, next_batch_offset),
                                            "IBD batch {}/{} fetched",
                                            batch_num,
                                            total_batches
                                        );
                                        swarm.behaviour_mut().request_beads(peer, &pruned_beads[next_batch_offset..(next_batch_offset+IBD_BATCH_SIZE)].to_vec());
                                    }
                                    else if next_batch_offset < pruned_beads.len() && ((next_batch_offset+IBD_BATCH_SIZE)>=pruned_beads.len()){
                                        let remaining = pruned_beads.len() - next_batch_offset;
                                        info!(
                                            offset = %next_batch_offset,
                                            remaining = %remaining,
                                            total = %pruned_beads.len(),
                                            "IBD final batch ({} beads remaining)",
                                            remaining
                                        );
                                        swarm.behaviour_mut().request_beads(peer, &pruned_beads[next_batch_offset..].to_vec());

                                    }
                                    else{
                                        //IBD completed
                                        let sync_mode = if next_batch_offset > IBD_BATCH_SIZE { "batches" } else { "single-fetch" };
                                        info!(
                                            peer = %peer,
                                            sync_mode = %sync_mode,
                                            "\u{1F389} IBD completed successfully via {}",
                                            sync_mode
                                        );
                                    }
                                }
                                 BeadResponse::GetBeadsAfter(bead_hashes)=>{
                                    //Getting all the beadhashes after the common oldest in both the peers
                                    let (tips_tx, tips_rx) = tokio::sync::oneshot::channel::<Vec<BeadHash>>();
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
                                        peer_manager.handle_fetch_tips(peer, tips_tx);
                                    }
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
                                {
                                    let mut peer_manager = peer_manager_arc.write().await;
                                    peer_manager.handle_update_incoming(peer, pruned);
                                }
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
                                        continue;
                                    }
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
                                        peer_manager.handle_update_ibd_peer_tips(peer, tips.0);
                                    }
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
                     SwarmCommand::InitiateIBD=>{
                        info!("Initiating IBD after peer discovery and selecting peer with lowest latency score");
                        //Evicting lowest latency peer id
                        let peer_ids = {
                            let peer_manager = peer_manager_arc.read().await;
                            peer_manager.get_top_k_peers_for_propagation(1)
                        };
                        if peer_ids.len() == 0 {
                            warn!("No peer available for syncing to take place");
                                tokio::spawn({
                                    let swarm_command_sender = swarm_command_sender.clone();
                                    //Retrying at fixed interval in case of no sync peers being available
                                    async move {
                                        tokio::time::sleep(Duration::from_secs(IBD_RETRY_DELAY)).await;
                                        match swarm_command_sender.send(SwarmCommand::InitiateIBD).await {
                                            Ok(_) => {
                                                warn!("Retrying IBD when no sync peers are available");
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
                                {
                                    let mut peer_manager = peer_manager_arc.write().await;
                                    peer_manager.handle_get_incoming_bead_retry_count(lowest_latency_peer,retry_count_tx);
                                }
                                let retry_cnt = match retry_count_rx.await {
                                    Ok(cnt) => cnt,
                                    Err(e) => {
                                        error!(error=?e, "Failed to receive retry count from IBDHandler, channel closed or sender dropped");
                                        continue;
                                    }
                                };
                                if retry_cnt >= MAX_IBD_RETRIES{
                                    warn!("Corresponding peer {:?} retries for IBD exceeded selecting next lowest latent peer",lowest_latency_peer);
                                    continue;
                                }
                                else if retry_cnt == 0{
                                    //First time syncing is being done wrt the provided peer
                                    let sync_start_request:BeadRequest = BeadRequest::GetTips;
                                    swarm.behaviour_mut().bead_sync.send_request(&lowest_latency_peer, sync_start_request);
                                    sync_request_sent = true;
                                    break;
                                }
                                else{
                                    //Case of retry is there
                                    {
                                        let mut peer_manager = peer_manager_arc.write().await;
                                        peer_manager.handle_update_retry_count(lowest_latency_peer);
                                    }
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
                                        tokio::time::sleep(Duration::from_secs(IBD_RETRY_DELAY)).await;
                                        match swarm_command_sender.send(SwarmCommand::InitiateIBD).await {
                                            Ok(_) => {
                                                warn!("Retrying IBD when no sync peers are available");
                                            }
                                            Err(error) => {
                                                error!(error=?error, "Failed to reinitiate IBD when no sync peer was available");
                                            }
                                        }
                                    }
                                });
                            }
                        }
                     },
                     SwarmCommand::PropagateMinedBead{
                        candidate_block,
                        extranonce_2_raw_value,
                        downstream_client_ip,
                        job_sent_timestamp,
                        downstream_payout_addr,
                        //TODO: Will be used as seperate entity after altering `uncommitted_metadata`
                        extranonce_1_raw_value,
                     }=>{
                        let (candidate_block_header, candidate_block_transactions) = candidate_block.into_parts();
                        let ids: Vec<Txid> = candidate_block_transactions
                            .iter()
                            .map(|tx| tx.compute_txid())
                            .collect();
                        let transaction_ids: Vec<Txid> = Vec::from(ids);
                        debug!("Broadcasting bead via floodsub");
                        //TODO:Currently temprorary placeholder will be replaced in upcoming PRs
                        let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
                            .parse::<bitcoin::PublicKey>()
                            .unwrap();
                        let mut time_hash_set = TimeVec(Vec::new());
                        let mut parent_hash_set: HashSet<BlockHash> = HashSet::new();
                        let mut braid_data = braid.write().await;
                        let tips_index = &braid_data.tips;
                        //Committing parents data in bead
                        for tip_bead in tips_index {
                            let current_tip_bead = braid_data.beads.get(*tip_bead).unwrap();
                            parent_hash_set.insert(current_tip_bead.block_header.block_hash());
                            time_hash_set
                                .0
                                .push(current_tip_bead.committed_metadata.start_timestamp);
                        }
                        debug!(tip_indices = ?tips_index, tip_hashes = ?parent_hash_set,
                            "Tips before extending the Braid");
                            //TODO:This will be replaced via the allotted `WeakShareDifficulty` after Difficulty adjustment
                            let weak_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
                            //Mindiff
                            let min_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
                        //Job sent time before downstream starts mining
                        let job_notification_time_val =
                        bitcoin::blockdata::locktime::absolute::Time::from_consensus(job_sent_timestamp)
                        .unwrap();
                    let candidate_block_bead_committed_metadata = CommittedMetadata {
                        comm_pub_key: public_key,
                        transaction_ids: TxIdVec(transaction_ids),
                        parents: parent_hash_set,
                        parent_bead_timestamps: time_hash_set,
                        payout_address: downstream_payout_addr.to_string(),
                        start_timestamp: job_notification_time_val,
                        min_target: min_target,
                        weak_target: weak_target,
                        miner_ip: downstream_client_ip.to_string(),
                    };
                    //TODO:This will be either be generated via the `Pubkey` from config parameter from `~/.braidpool`
                    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
                    let sig = Signature {
                        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
                        sighash_type: EcdsaSighashType::All,
                    };
                    //Current UNIX timestamp during broadcast of bead
                    let current_system_time = std::time::SystemTime::now();
                    let duration_since_epoch = match current_system_time.duration_since(UNIX_EPOCH) {
                        Ok(duration) => duration,
                        Err(error) => {
                            error!(error = ?error, "System time before UNIX EPOCH");
                            continue;
                        }
                    };

                    let unix_timestamp = duration_since_epoch.as_secs().to_u32().unwrap();

                    let candidate_block_bead_uncommitted_metadata = UnCommittedMetadata {
                        broadcast_timestamp: bitcoin::blockdata::locktime::absolute::MedianTimePast::from_u32(
                            unix_timestamp,
                        )
                        .unwrap(),
                        extra_nonce_1: extranonce_1_raw_value,
                        extra_nonce_2: extranonce_2_raw_value,
                        signature: sig,
                    };
                    let weak_share = Bead {
                        committed_metadata: candidate_block_bead_committed_metadata,
                        block_header: candidate_block_header,
                        uncommitted_metadata: candidate_block_bead_uncommitted_metadata,
                    };
                    let status = braid_data.extend(&weak_share);
                    let curr_bead_hash = weak_share.block_header.block_hash();
                    let bead_index_mapping = braid_data.bead_index_mapping.clone();
                    match status {
                            AddBeadStatus::BeadAdded => {
                                let new_tips: Vec<_> = braid_data.tips.iter().map(|&idx| idx).collect();
                                info!(
                                    hash = %curr_bead_hash,
                                    new_tips = ?new_tips,
                                    "Braid extended successfully"
                                );
                                let bead_id = bead_index_mapping
                                .get(&weak_share.block_header.block_hash())
                                .unwrap()
                                .0;
                                //In case of self-mined bead we won't have any orphan beads removed
                                let _db_insertion_command = match db_tx.send(node::db::BraidpoolDBTypes::InsertTupleTypes { query: node::db::InsertTupleTypes::InsertBeadSequentially { bead_to_insert: weak_share.clone(),removed_orphans:Vec::new(),bead_index_mapping:bead_index_mapping,bead_id:bead_id} })
                                        .await
                                    {
                                        Ok(_) => {
                                            debug!(
                                                hash = %curr_bead_hash,
                                                "InsertBeadSequentially sent to DB thread"
                                            );
                                        }
                                        Err(error) => {
                                            error!(error = ?error, "Database insertion command failed");
                                        }
                                    };
                                    let serialized_weak_share_bytes = bitcoin::consensus::serialize(&weak_share);
                                swarm
                                .behaviour_mut()
                                .bead_announce
                                .publish(current_broadcast_topic.clone(), serialized_weak_share_bytes);
                                info!(topic = ?current_broadcast_topic, "Published bead to floodsub topic");
                            }
                            _ => {
                                warn!(status = ?status, hash = %weak_share.block_header.block_hash(),
                                    "Failed to extend Braid")
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
