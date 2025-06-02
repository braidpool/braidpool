use clap::Parser;
use futures::StreamExt;
use libp2p::{
    core::multiaddr::Multiaddr,
    identify, ping,
    swarm::{NetworkBehaviour, SwarmEvent},
};
use std::error::Error;
use std::fs;
use std::time::Duration;
use tokio::sync::mpsc;

mod block_template;
mod cli;
mod rpc;
mod zmq;

#[derive(NetworkBehaviour)]
struct NodeBehaviour {
    identify: libp2p::identify::Behaviour,
    ping: libp2p::ping::Behaviour,
}

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

    let mut swarm = libp2p::SwarmBuilder::with_new_identity()
        .with_tokio()
        .with_quic()
        .with_behaviour(|key| NodeBehaviour {
            identify: identify::Behaviour::new(identify::Config::new(
                "/braidpool/id/1.0.0".to_string(),
                key.public(),
            )),
            ping: ping::Behaviour::default(),
        })?
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

    swarm.listen_on(multi_addr.clone())?;

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
    // Spawn a tokio task to handle the swarm events
    let swarm_handle = tokio::spawn(async move {
        loop {
            match swarm.select_next_some().await {
                SwarmEvent::NewListenAddr { address, .. } => println!("Listening on {:?}", address),
                // Prints peer id identify info is being sent to.
                SwarmEvent::Behaviour(NodeBehaviourEvent::Identify(identify::Event::Sent {
                    peer_id,
                    ..
                })) => {
                    log::info!("Sent identify info to {:?}", peer_id);
                }
                // Prints out the info received via the identify event
                SwarmEvent::Behaviour(NodeBehaviourEvent::Identify(
                    identify::Event::Received { info, .. },
                )) => {
                    log::info!("Received {:?}", info);
                }
                SwarmEvent::Behaviour(NodeBehaviourEvent::Identify(identify::Event::Error {
                    peer_id,
                    error,
                    connection_id: _,
                })) => {
                    log::error!("Error in identify event for peer {}: {:?}", peer_id, error);
                }
                SwarmEvent::Behaviour(NodeBehaviourEvent::Ping(ping::Event {
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
                }
                _ => {}
            }
        }
    });

    tokio::signal::ctrl_c().await?;
    println!("Shutting down...");

    swarm_handle.abort();

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
