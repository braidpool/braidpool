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
    bead,
    behaviour::{self, BEAD_ANNOUNCE_PROTOCOL},
};
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::{collections::HashSet, error::Error};
use std::{fs, time::Duration};
use tokio::sync::mpsc;

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
        loop {
            tokio::select! {

                event = swarm.select_next_some() => {
                    match event {
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
                                ..
                            },
                        )) => {
                            log::error!("Error in identify event for peer {}: {:?}", peer_id, error);
                        }

                        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Ping(ping::Event {
                            peer,
                            result,
                            ..
                        })) => {
                            log::info!("Response from peer: {} with result: {:?}", peer, result);
                        }

                        SwarmEvent::ConnectionEstablished {
                            peer_id, endpoint, ..
                        } => {
                            log::info!(
                                "Connection established to peer: {} via {}",
                                peer_id,
                                endpoint.get_remote_address()
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
                                    match request {
                                        bead::BeadRequest::GetBeads(hashes) => {
                                            let beads = Vec::new();
                                            swarm.behaviour_mut().respond_with_beads(channel, beads);
                                        }
                                        bead::BeadRequest::GetTips => {
                                            let tips = HashSet::new();
                                            swarm.behaviour_mut().respond_with_tips(channel, tips);
                                        }
                                        bead::BeadRequest::GetGenesis => {
                                            let genesis = HashSet::new();
                                            swarm.behaviour_mut().respond_with_genesis(channel, genesis);
                                        }
                                    }
                                }
                                request_response::Message::Response {
                                    request_id,
                                    response,
                                } => {
                                    match response {
                                        bead::BeadResponse::Beads(beads) => {
                                            // Handle beads
                                        }
                                        bead::BeadResponse::Tips(tips) => {
                                            // Handle tips
                                        }
                                        bead::BeadResponse::Genesis(genesis) => {
                                            // Handle genesis
                                        }
                                        bead::BeadResponse::Error(error) => {
                                            // Handle error
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
