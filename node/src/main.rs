use bitcoin::consensus::encode::deserialize;
use clap::Parser;
use futures::StreamExt;
use libp2p::{
    core::multiaddr::Multiaddr,
    floodsub, identify,
    identity::Keypair,
    kad::{self, Mode, QueryResult},
    ping, request_response,
    swarm::SwarmEvent,
    PeerId,
};
use node::{
    bead::{self, Bead, BeadRequest},
    behaviour::{self, BEAD_ANNOUNCE_PROTOCOL},
    braid, cli,
    error::IPCtemplateError,
    ipc,
    peer_manager::PeerManager,
    rpc_server::{parse_arguments, run_rpc_server},
};
use std::error::Error;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::sync::Arc;
use std::{fs, time::Duration};
use tokio::sync::RwLock;
use tokio_util::sync::CancellationToken;

use behaviour::{BraidPoolBehaviour, BraidPoolBehaviourEvent};

use crate::behaviour::KADPROTOCOLNAME;
//boot nodes peerIds
const BOOTNODES: [&str; 1] = ["12D3KooWCXH2BiENJ7NkFUBSavd8Ed4ZSYKNdiFnYP5abSo36rGL"];
//dns NS
const SEED_DNS: &str = "/dnsaddr/french.braidpool.net";
//combined addr for dns resolution and dialing of boot for peer discovery
const ADDR_REFRENCE: &str =
    "/dnsaddr/french.braidpool.net/p2p/12D3KooWCXH2BiENJ7NkFUBSavd8Ed4ZSYKNdiFnYP5abSo36rGL";
use tokio::sync::mpsc;

mod block_template;
mod rpc;
mod zmq;

#[allow(dead_code)]
mod common_capnp;
mod echo_capnp;
#[allow(dead_code)]
mod init_capnp;
mod mining_capnp;
#[allow(dead_code)]
mod proxy_capnp;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let (main_shutdown_tx, mut main_shutdown_rx) =
        mpsc::channel::<tokio::signal::unix::SignalKind>(32);
    let main_task_token = CancellationToken::new();
    let ipc_task_token = main_task_token.clone();
    let args = cli::Cli::parse();
    setup_logging();
    setup_tracing()?;
    let datadir = shellexpand::full(args.datadir.to_str().unwrap()).unwrap();
    match fs::metadata(&*datadir) {
        Ok(m) => {
            if !m.is_dir() {
                log::error!("Data directory {} exists but is not a directory", datadir);
            }
            log::info!("Using existing data directory: {}", datadir);
        }
        Err(_) => {
            log::info!("Creating data directory: {}", datadir);
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
                log::warn!(
                    "Keystore permissions are not secure: {:o}, setting to 0o400",
                    perms.mode() & 0o777
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
            log::info!("Loading existing keypair from keystore...");
            libp2p::identity::Keypair::from_protobuf_encoding(&keypair).map_err(|e| {
                log::error!("Failed to read keypair from keystore: {}", e);
                e
            })?
        }
        Err(_) => {
            log::info!("No existing keypair found, generating new keypair...");
            let keypair: Keypair = libp2p::identity::Keypair::generate_ed25519();
            let keypair_bytes = keypair.to_protobuf_encoding()?;
            fs::write(&keystore_path, keypair_bytes)?;
            #[cfg(unix)]
            {
                let mut perms = fs::metadata(&keystore_path)?.permissions();
                perms.set_mode(0o400);
                fs::set_permissions(&keystore_path, perms)?;
                log::info!("Set keystore file permissions to 0o400");
            }
            keypair
        }
    };

    let genesis_beads = Vec::from([]);
    // Initializing the braid object with read write lock
    //for supporting concurrent readers and single writer
    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    //spawning the rpc server
    if let Some(rpc_command) = args.command {
        let server_address = tokio::spawn(run_rpc_server(Arc::clone(&braid)));
        let socket_address = server_address.await.unwrap().unwrap();
        let parsing_handle =
            tokio::spawn(parse_arguments(rpc_command, socket_address.clone())).await;
    } else {
        //running the rpc server and updating the reference counter
        //for shared ownership
        let server_handler = tokio::spawn(run_rpc_server(Arc::clone(&braid))).await;
    }
    // load beads from db (if present) and insert in braid here
    // Initializing the peer manager
    let mut peer_manager = PeerManager::new(8);

    //For local testing uncomment this keypair peer since it running to process will
    //result in same peerID leading to OutgoingConnectionError

    // let keypair = identity::Keypair::generate_ed25519();
    //creating a main topic subscribing to the current test topic
    let current_broadcast_topic: floodsub::Topic = floodsub::Topic::new("braidpool_channel");

    let mut swarm = libp2p::SwarmBuilder::with_existing_identity(keypair)
        .with_tokio()
        .with_quic()
        .with_dns()
        .unwrap()
        .with_behaviour(|local_key| BraidPoolBehaviour::new(local_key).unwrap())?
        .with_swarm_config(|cfg| cfg.with_idle_connection_timeout(Duration::from_secs(u64::MAX)))
        .build();
    log::info!("Local Peerid: {}", swarm.local_peer_id());
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
    log::info!("Boot nodes have been added to the node's local DHT");
    swarm.dial(ADDR_REFRENCE.parse::<Multiaddr>().unwrap())?;
    log::info!("Boot Node dialied with listening addr {:?}", ADDR_REFRENCE);
    //IPC(inter process communication) based `getblocktemplate` and `notification` to send to the downstream via the `cmempoold` architecture
    if args.ipc {
        log::info!("Socket path: {}", args.ipc_socket);

        let (ipc_template_tx, ipc_template_rx) = mpsc::channel::<Vec<u8>>(1);

        let ipc_socket_path = args.ipc_socket.clone();

        let ipc_handler = tokio::task::spawn_blocking(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("Failed to create tokio runtime");
            rt.block_on(async {
                let local_set = tokio::task::LocalSet::new();

                local_set
                    .run_until(async {
                        let listener_task = tokio::task::spawn_local({
                            let ipc_socket_path = ipc_socket_path.clone();
                            let ipc_template_tx = ipc_template_tx.clone();
                            async move {
                                loop {
                                    match ipc::ipc_block_listener(
                                        ipc_socket_path.clone(),
                                        ipc_template_tx.clone(),
                                    )
                                    .await
                                    {
                                        Ok(_) => {
                                            break;
                                        }
                                        Err(e) => {
                                            log::error!("IPC block listener failed: {}", e);
                                            log::info!("Restarting IPC listener in 10 seconds...");
                                            tokio::time::sleep(tokio::time::Duration::from_secs(
                                                10,
                                            ))
                                            .await;
                                        }
                                    }
                                }
                            }
                        });

                        let consumer_task = tokio::task::spawn_local(async move {
                            ipc_template_consumer(ipc_template_rx).await.unwrap();
                        });
                        tokio::select! {
                            _ = listener_task => log::info!("IPC listener completed"),
                            _ = consumer_task => log::info!("IPC consumer completed"),
                            _= ipc_task_token.cancelled()=>{
                                log::info!("Token cancelled from the parent Task, shutting down IPC task");
                            }
                        }
                    })
                    .await;
            });
        });
    } else {
        log::info!("Using ZMQ for Bitcoin Core communication");
        log::info!("ZMQ URL: tcp://{}:{}", args.bitcoin, args.zmqhashblockport);
        let rpc = rpc::setup(
            args.bitcoin.clone(),
            args.rpcport,
            args.rpcuser,
            args.rpcpass,
            args.rpccookie,
        )?;
        let (zmq_template_tx, zmq_template_rx) = mpsc::channel(1);
        let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);
        tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, zmq_template_tx));
        tokio::spawn(block_template::consumer(zmq_template_rx));
    }
    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            let node_multiaddr: Multiaddr = node.parse().expect("Failed to parse to multiaddr");
            let dial_result = swarm.dial(node_multiaddr.clone());
            if let Some(err) = dial_result.err() {
                log::error!(
                    "Failed to dial node: {} with error: {}",
                    node_multiaddr,
                    err
                );
                continue;
            }
            log::info!("Dialed : {}", node_multiaddr);
        }
    };
    let swarm_handle = tokio::spawn(async move {
        let braid = std::sync::Arc::clone(&braid);
        loop {
            match swarm.select_next_some().await {
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Kademlia(
                    kad::Event::RoutingUpdated {
                        peer,
                        is_new_peer,
                        addresses,
                        bucket_range,
                        old_peer,
                    },
                )) => {
                    log::info!(
                        "Routing updated for peer: {peer}, new: {is_new_peer}, addresses: {:?}, bucket: {:?}, old_peer: {:?}",
                        addresses, bucket_range, old_peer
                    );
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                    floodsub::FloodsubEvent::Subscribed { peer_id, topic },
                )) => {
                    log::info!(
                        "A new peer {:?} subscribed to the topic {:?}",
                        peer_id,
                        topic
                    );
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                    floodsub::FloodsubEvent::Unsubscribed { peer_id, topic },
                )) => {
                    log::info!(
                        "A peer {:?} unsubsribed from the topic {:?}",
                        peer_id,
                        topic
                    );
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                    floodsub::FloodsubEvent::Message(message),
                )) => {
                    log::info!(
                        "{:?} Message has been recieved  from the peer {:?} and having data {:?}",
                        message.topics,
                        message.source,
                        message.data
                    );
                    let result_bead: Result<Bead, bitcoin::consensus::DeserializeError> =
                        deserialize(&message.data);
                    match result_bead {
                        Ok(bead) => {
                            log::info!("Received bead: {:?}", bead);
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
                                    log::warn!("No peers available to request parents");
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
                            log::error!("Failed to deserialize bead: {}", e);
                        }
                    }
                }
                SwarmEvent::NewListenAddr { address, .. } => {
                    log::info!("Listening on {:?}", address)
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(
                    identify::Event::Sent { peer_id, .. },
                )) => {
                    log::info!("Sent identify info to {:?}", peer_id);
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(
                    identify::Event::Received { info, peer_id, .. },
                )) => {
                    let info_reference = info.clone();
                    if info.protocols.iter().any(|p| *p == KADPROTOCOLNAME) {
                        for addr in info.listen_addrs {
                            log::info!("received addr {addr} through identify");
                            swarm.behaviour_mut().kademlia.add_address(&peer_id, addr);
                        }
                    } else {
                        log::info!("The peer was not added to the local DHT ");
                    }
                    if info_reference
                        .clone()
                        .protocols
                        .iter()
                        .any(|p| *p == BEAD_ANNOUNCE_PROTOCOL)
                    {
                        log::info!("PEER ADDED TO FLOODSUB MESH {:?}", peer_id);
                        for _addr in info_reference.clone().listen_addrs {
                            swarm
                                .behaviour_mut()
                                .bead_announce
                                .add_node_to_partial_view(peer_id);
                        }
                    } else {
                        log::info!(
                            "The peer listening at {:?} was not added to the floodsub mesh",
                            info_reference.observed_addr
                        );
                    }
                    log::info!("Received {:?}", info_reference);
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Kademlia(
                    kad::Event::OutboundQueryProgressed { result, .. },
                )) => match result {
                    QueryResult::GetClosestPeers(Ok(ok)) => {
                        log::info!("Got closest peers: {:?}", ok.peers);
                    }
                    QueryResult::GetClosestPeers(Err(err)) => {
                        log::info!("Failed to get closest peers: {err}");
                    }
                    _ => log::info!("Other query result: {:?}", result),
                },
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(
                    identify::Event::Error {
                        peer_id,
                        error,
                        connection_id: _,
                    },
                )) => {
                    log::error!("Error in identify event for peer {}: {:?}", peer_id, error);
                }
                SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Ping(ping::Event {
                    peer,
                    result,
                    ..
                })) => {
                    log::info!(
                        "Ping result for peer {}: {:?}",
                        peer,
                        match result {
                            Ok(latency) => format!("Latency: {} ms", latency.as_millis()),
                            Err(err) => format!("Error: {}", err),
                        }
                    );
                }
                SwarmEvent::ConnectionEstablished {
                    peer_id, endpoint, ..
                } => {
                    // Add the peer to the peer manager
                    let remote_addr = endpoint.get_remote_address();
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
                    log::info!(
                        "Connection established to peer: {} via {}",
                        peer_id,
                        remote_addr
                    );
                }
                SwarmEvent::ConnectionClosed {
                    peer_id,
                    connection_id,
                    endpoint,
                    num_established,
                    cause,
                } => {
                    log::info!("Connection closed to peer: {} with connection id: {} via {}. Number of established connections: {}. Cause: {:?}", peer_id,connection_id,endpoint.get_remote_address(), num_established,cause);
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
                    log::info!(
                        "Received bead sync message from peer: {}: {:?}. Connection-id: {:?}",
                        peer,
                        message,
                        connection_id
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
                                    log::info!("Received tips: {:?}", tips);
                                }
                                bead::BeadResponse::Genesis(genesis) => {
                                    log::info!("Received genesis beads: {:?}", genesis);
                                    let status = {
                                        let braid_lock = braid.read().await;
                                        braid_lock.check_genesis_beads(&genesis)
                                    };
                                    match status {
                                        braid::GenesisCheckStatus::GenesisBeadsValid => {
                                            log::info!("Genesis beads are valid");
                                        }
                                        braid::GenesisCheckStatus::MissingGenesisBead => {
                                            log::warn!("Missing genesis bead");
                                        }
                                        braid::GenesisCheckStatus::GenesisBeadsCountMismatch => {
                                            log::warn!("Genesis beads count mismatch");
                                        }
                                    }
                                }
                                bead::BeadResponse::Error(error) => {
                                    log::error!("Error in bead sync response: {:?}", error);
                                    peer_manager.update_score(&peer, -1.0);
                                }
                            };
                        }
                    }
                }
                event => {
                    log::info!("{:?}", event);
                }
            }
        }
    });

    //gracefull shutdown via `Cancellation token`
    let shutdown_signal = tokio::signal::ctrl_c().await;
    match shutdown_signal {
        Ok(_) => {
            log::info!("Shutting down the Network Swarm");
            swarm_handle.abort();
            tokio::time::sleep(Duration::from_millis(1)).await;
            #[allow(unused)]
            let shutdown_sub_tasks = match main_shutdown_tx
                .send(tokio::signal::unix::SignalKind::interrupt())
                .await
            {
                Ok(_) => {
                    log::info!("Sub-tasks have been INTERRUPTED kindly wait for them to shutdown");
                    main_task_token.cancel();
                }
                Err(error) => {
                    log::error!(
                        "An error running while sending INTERUPPT to the sub tasks - {:?}",
                        error
                    );
                }
            };
        }
        Err(error) => {
            log::error!(
                "An error occurred while shutting down the braid node {:?}",
                error
            );
        }
    }

    Ok(())
}

async fn ipc_template_consumer(
    mut template_rx: mpsc::Receiver<Vec<u8>>,
) -> Result<(), IPCtemplateError> {
    while let Some(template_bytes) = template_rx.recv().await {
        if template_bytes.len() > 0 {
            // Process the template bytes as needed
            // For example, you could deserialize it or log its contents
            // let hex_string = bytes_to_hex(&template_bytes);
            // log::info!("Template in hex: {}", hex_string);
        } else {
            log::warn!("IPC template too short: 0 bytes");
        }
    }

    Ok(())
}

fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

fn setup_tracing() -> Result<(), Box<dyn Error>> {
    // Create a filter for controlling the verbosity of tracing output
    let filter =
        tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);

    // Build a `tracing` subscriber with the specified filter
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    // Set the subscriber as the global default for tracing
    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber failed");

    Ok(())
}
