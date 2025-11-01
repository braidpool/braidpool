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
use node::db::db_handlers::fetch_beads_in_batch;
use node::SwarmHandler;
use node::{
    bead::{self, Bead, BeadRequest},
    behaviour::{self, BEAD_ANNOUNCE_PROTOCOL, BRAIDPOOL_TOPIC},
    braid, cli,
    db::db_handlers::DBHandler,
    ipc_template_consumer,
    peer_manager::PeerManager,
    rpc_server::{parse_arguments, run_rpc_server},
    setup_tracing,
    stratum::{BlockTemplate, ConnectionMapping, Notifier, NotifyCmd, Server, StratumServerConfig},
    SwarmCommand, TemplateId,
};
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::sync::Arc;
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
    let genesis_beads = Vec::from([]);
    // Initializing the braid object with read write lock
    //for supporting concurrent readers and single writer
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    //Initializing DB and db command handler
    let (mut _db_handler, db_tx) = DBHandler::new(Arc::clone(&braid)).await.unwrap();
    let db_connection_pool = _db_handler.db_connection_pool.clone();
    //Reconstructing local braid upon startup
    let db_connection_pool_ref = _db_handler.db_connection_pool.clone();
    let braid_ref = braid.clone();
    // FIXME instead we should look 144 blocks back from the bitcoin tip (1 day) and load beads
    // starting from that block as genesis
    let initial_bead_fetch_handle = tokio::spawn(async move {
        let mut guard = braid_ref.write().await;
        let fetched_beads = fetch_beads_in_batch(db_connection_pool_ref, 1000)
            .await
            .unwrap();
        for bead in &fetched_beads {
            let curr_bead_status = guard.extend(&bead);
            debug!(
                hash = ?bead.block_header.block_hash(),
                status = ?curr_bead_status,
                "Bead inserted"
            );
        }
        info!(beads = fetched_beads.len(), "Beads loaded from DB");
    });
    let _yield_result = initial_bead_fetch_handle.await.unwrap();
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
    let (swarm_handler, mut swarm_command_receiver) = SwarmHandler::new(Arc::clone(&braid), db_tx);
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
    let datadir = shellexpand::full(args.datadir.to_str().unwrap()).unwrap();
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
        let socket_address = server_address.await.unwrap().unwrap();
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

    let mut swarm = libp2p::SwarmBuilder::with_existing_identity(keypair)
        .with_tokio()
        .with_quic()
        .with_dns()
        .unwrap()
        .with_behaviour(|local_key| BraidPoolBehaviour::new(local_key).unwrap())?
        .with_swarm_config(|cfg| cfg.with_idle_connection_timeout(Duration::from_secs(u64::MAX)))
        .build();
    let socket_addr: std::net::SocketAddr = match args.bind.parse() {
        Ok(addr) => addr,
        Err(_) => format!("{}:6680", args.bind)
            .parse()
            .expect("Failed to parse bind address"),
    };
    let multi_addr: Multiaddr = format!(
        "/ip4/{}/udp/{}/quic-v1",
        socket_addr.ip(),
        socket_addr.port()
    )
    .parse()
    .expect("Failed to create multiaddress");
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
        swarm.behaviour_mut().kademlia.add_address(
            &boot_peer.parse::<PeerId>().unwrap(),
            SEED_DNS.parse::<Multiaddr>().unwrap(),
        );
    }
    info!(boot_node_count = %BOOTNODES.len(), "Boot nodes added to DHT");
    swarm.dial(ADDR_REFRENCE.parse::<Multiaddr>().unwrap())?;
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
            let node_multiaddr: Multiaddr = node.parse().expect("Failed to parse to multiaddr");
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
                         let result_bead: Result<Bead, bitcoin::consensus::DeserializeError> =
                             deserialize(&message.data);
                         match result_bead {
                             Ok(bead) => {
                                 info!(bead = ?bead, hash = %bead.block_header.block_hash(), "Received bead");
                                 // Handle the received bead here
                                 let status = {
                                     let mut braid_lock = braid.write().await;
                                     braid_lock.extend(&bead)
                                 };
                                 if let braid::AddBeadStatus::ParentsNotYetReceived = status {
                                     //request the parents using request response protocol
                                     let peer_id = peer_manager.get_top_k_peers_for_propagation(1);
                                     if let Some(peer) = peer_id.first() {
                                         swarm.behaviour_mut().bead_sync.send_request(
                                             &peer,
                                             BeadRequest::GetBeads(
                                                 bead.committed_metadata.parents.clone(),
                                             ),
                                         );
                                     } else {
                                         warn!(parent_count = %bead.committed_metadata.parents.len(), "Insufficient peers for bead sync");
                                     }
                                 } else if let braid::AddBeadStatus::InvalidBead = status {
                                     // update the peer manager about the invalid bead
                                     peer_manager.penalize_for_invalid_bead(&message.source);
                                 } else if let braid::AddBeadStatus::BeadAdded = status {
                                     // update score of the peer
                                     peer_manager.update_score(&message.source, 1.0);
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
                                     bead::BeadRequest::GetBeads(hashes) => {
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
                                         swarm.behaviour_mut().respond_with_beads(channel, beads);
                                     }
                                     bead::BeadRequest::GetTips => {
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
                                     bead::BeadRequest::GetGenesis => {
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
                                     bead::BeadRequest::GetAllBeads => {
                                         let all_beads;
                                         {
                                             let braid_lock = braid.read().await;
                                             all_beads = braid_lock.beads.iter().cloned().collect();
                                         }
                                         swarm.behaviour_mut().respond_with_beads(channel, all_beads);
                                     }
                                 }
                             }
                             request_response::Message::Response {
                                 request_id: _,
                                 response,
                             } => {
                                 match response {
                                     bead::BeadResponse::Beads(beads)
                                     | bead::BeadResponse::GetAllBeads(beads) => {
                                         let mut braid_lock = braid.write().await;
                                         for bead in beads {
                                             let status = braid_lock.extend(&bead);
                                             if let braid::AddBeadStatus::InvalidBead = status {
                                                 // update the peer manager about the invalid bead
                                                 peer_manager.penalize_for_invalid_bead(&peer);
                                             } else if let braid::AddBeadStatus::BeadAdded = status {
                                                 // update score of the peer
                                                 peer_manager.update_score(&peer, 1.0);
                                             }
                                         }
                                     }
                                     // no use of this arm as of now
                                     bead::BeadResponse::Tips(tips) => {
                                         info!(tips = ?tips, tip_count = %tips.len(), "Received braid tips");
                                     }
                                     bead::BeadResponse::Genesis(genesis) => {
                                         info!(genesis = ?genesis, genesis_count = %genesis.len(), "Received genesis beads");
                                         let status = {
                                             let braid_lock = braid.read().await;
                                             braid_lock.check_genesis_beads(&genesis)
                                         };
                                         match status {
                                             braid::GenesisCheckStatus::GenesisBeadsValid => {
                                                 info!(count = %genesis.len(), "Genesis beads validated");
                                             }
                                             braid::GenesisCheckStatus::MissingGenesisBead => {
                                                 warn!(peer = %peer, "Missing genesis bead");
                                             }
                                             braid::GenesisCheckStatus::GenesisBeadsCountMismatch => {
                                                 warn!(
                                                     received = %genesis.len(),
                                                     peer = %peer,
                                                     "Genesis bead count mismatch"
                                                 );
                                             }
                                         }
                                     }
                                     bead::BeadResponse::Error(error) => {
                                         error!(error = ?error, "Bead sync response error");
                                         peer_manager.update_score(&peer, -1.0);
                                     }
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
