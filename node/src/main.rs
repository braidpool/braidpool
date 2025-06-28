use bitcoin::consensus::encode::deserialize;
use clap::Parser;
use futures::StreamExt;
use libp2p::kad::RecordKey;
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
    bead::{self, Bead},
    behaviour::{self, BEAD_ANNOUNCE_PROTOCOL},
    braid, committed_metadata,
    peer_manager::PeerManager,
    uncommitted_metadata, utils,
};
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::sync::Arc;
use std::{collections::HashSet, error::Error};
use std::{fs, time::Duration};
use tokio::sync::{mpsc, Mutex};

mod block_template;
mod cli;
mod config;
mod rpc;
mod zmq;

use behaviour::{BraidPoolBehaviour, BraidPoolBehaviourEvent};

use crate::behaviour::KADPROTOCOLNAME;
//boot nodes peerIds
const BOOTNODES: [&str; 1] = ["12D3KooWCXH2BiENJ7NkFUBSavd8Ed4ZSYKNdiFnYP5abSo36rGL"];
//dns NS
const SEED_DNS: &str = "/dnsaddr/french.braidpool.net";
//combined addr for dns resolution and dialing of boot for peer discovery
const ADDR_REFRENCE: &str =
    "/dnsaddr/french.braidpool.net/p2p/12D3KooWCXH2BiENJ7NkFUBSavd8Ed4ZSYKNdiFnYP5abSo36rGL";

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
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

    let rpc = rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
        args.rpccookie,
    )?;
    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);

    let (block_template_tx, block_template_rx) = mpsc::channel(1);
    tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, block_template_tx));
    tokio::spawn(block_template::consumer(block_template_rx));

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

    // Initializing the braid object
    let mut braid = Arc::new(Mutex::new(braid::Braid::new(
        HashSet::new(), // beads
    )));
    // load beads from db (if present) and insert in braid here
    // Initializing the peer manager
    let peer_manager = PeerManager::new(8);

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
    println!("Local Peerid: {}", swarm.local_peer_id());
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
                            let mut braid_lock = braid.lock().await;
                            let status = braid_lock.extend(&bead);
                            
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
                        for addr in info_reference.clone().listen_addrs {
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
                            request_id,
                            channel,
                        } => {
                            // Handle the bead sync request here
                            match request {
                                bead::BeadRequest::GetBeads(hashes) => {
                                    // Get the beads from the local store
                                    let beads = Vec::new(); // Replace with actual logic to fetch beads
                                    swarm.behaviour_mut().respond_with_beads(channel, beads);
                                }
                                bead::BeadRequest::GetTips => {
                                    // Get the tips from the local store
                                    let tips = HashSet::new(); // Replace with actual logic to fetch tips
                                    swarm.behaviour_mut().respond_with_tips(channel, tips);
                                }
                                bead::BeadRequest::GetGenesis => {
                                    // Get the genesis beads from the local store
                                    let genesis = HashSet::new(); // Replace with actual logic to fetch genesis
                                    swarm.behaviour_mut().respond_with_genesis(channel, genesis);
                                }
                            }
                        }
                        request_response::Message::Response {
                            request_id,
                            response,
                        } => {
                            match response {
                                // might consider spawning this task on the blocking threadpool if the ex. time is more
                                bead::BeadResponse::Beads(beads) => {
                                    tokio::task::spawn_blocking({
                                        || {
                                            // let mut lock = braid.lock().await;
                                            // lock.handle_beads(peer, beads);
                                        }
                                    });
                                }
                                bead::BeadResponse::Tips(tips) => {
                                    tokio::task::spawn_blocking({
                                        || {
                                            // let mut lock = braid.lock().await;
                                            // lock.handle_tips(peer, tips);
                                        }
                                    });
                                }
                                bead::BeadResponse::Genesis(genesis) => {
                                    tokio::task::spawn_blocking({
                                        || {
                                            // let mut lock = braid.lock().await;
                                            // lock.handle_genesis(peer, genesis);
                                        }
                                    });
                                }
                                bead::BeadResponse::Error(error) => {
                                    tokio::task::spawn_blocking({
                                        || {
                                            // let mut lock = braid.lock().await;
                                            // lock.handle_error(peer, error);
                                        }
                                    });
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

    //gracefull shutdown
    let shutdown_signal = tokio::signal::ctrl_c().await;
    match shutdown_signal {
        Ok(_) => {
            println!("Shutting down...");
            swarm_handle.abort();
        }
        Err(error) => {
            println!(
                "An error occurred while shutting down the braid node {:?}",
                error
            );
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
