use clap::Parser;
use std::error::Error;

mod cli;
mod p2p;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = cli::Cli::parse();

    setup_logging();
    setup_tracing()?;

    let datadir = args.datadir;
    log::info!("Using braid data directory: {}", datadir.display());

    // create `P2pEngine` and get configs for the protocols that it will use.
    let (engine, bead_announce_config, braid_sync_config) = p2p::P2pEngine::new();

    // build `Litep2pConfig`
    let multiaddr = format!("/ip4/127.0.0.1/udp/{}/quic-v1", args.bindport);
    let config = litep2p::config::Litep2pConfigBuilder::new()
        .with_quic(litep2p::transport::quic::config::TransportConfig {
            listen_address: multiaddr.parse().unwrap(),
        })
        .with_notification_protocol(bead_announce_config)
        .with_request_response_protocol(braid_sync_config)
        .build();

    // create `Litep2p` object and start internal protocol handlers and the QUIC transport
    let mut litep2p = litep2p::Litep2p::new(config).await.unwrap();

    // notify multiaddr
    log::info!(
        "Braidpool node multiaddr: {}",
        litep2p.listen_addresses().next().unwrap()
    );

    // spawn `P2pEngine` in the background
    tokio::spawn(engine.run());

    // dial peers
    if let Some(peers) = args.addpeer {
        for peer_multiaddr in peers.iter() {
            log::info!("Connecting to node: {:?}", peer_multiaddr);
            litep2p
                .dial_address(peer_multiaddr.parse().unwrap())
                .await
                .unwrap();
        }
    }

    // poll `litep2p` to allow connection-related activity to make progress
    loop {
        match litep2p.next_event().await.unwrap() {
            litep2p::Litep2pEvent::ConnectionEstablished { address, .. } => {
                log::info!("Connection established with {}", address);
            }
            _ => {}
        }
    }
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
