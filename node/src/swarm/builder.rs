use std::{error::Error, net::SocketAddr};

use libp2p::{core::multiaddr::Multiaddr, identity::Keypair, Swarm};

use crate::behaviour::BraidPoolBehaviour;

use super::config::IDLE_CONNECTION_TIMEOUT;

/// Configuration for building a swarm.
pub struct SwarmConfig {
    /// The node's cryptographic identity.
    pub keypair: Keypair,
    /// Socket address to bind to.
    pub bind_addr: SocketAddr,
}

impl SwarmConfig {
    /// Creates a new SwarmConfig.
    pub fn new(keypair: Keypair, bind_addr: SocketAddr) -> Self {
        Self { keypair, bind_addr }
    }

    /// Converts the bind address to a libp2p Multiaddr (QUIC).
    pub fn to_multiaddr(&self) -> Result<Multiaddr, Box<dyn Error>> {
        let multi_addr: Multiaddr = format!(
            "/ip4/{}/udp/{}/quic-v1",
            self.bind_addr.ip(),
            self.bind_addr.port()
        )
        .parse()
        .map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("Failed to create multiaddress: {}", e),
            )
        })?;

        Ok(multi_addr)
    }
}

/// Builds a configured libp2p swarm.
pub async fn build_swarm(config: SwarmConfig) -> Result<Swarm<BraidPoolBehaviour>, Box<dyn Error>> {
    let swarm_builder = libp2p::SwarmBuilder::with_existing_identity(config.keypair)
        .with_tokio()
        .with_quic()
        .with_dns()
        .map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("DNS setup failed: {:?}", e),
            )
        })?;

    let swarm = swarm_builder
        .with_behaviour(|local_key| {
            BraidPoolBehaviour::new(local_key).expect(
                "Failed to create BraidPoolBehaviour - check keypair and network configuration",
            )
        })?
        .with_swarm_config(|cfg| cfg.with_idle_connection_timeout(IDLE_CONNECTION_TIMEOUT))
        .build();

    Ok(swarm)
}

/// Parses a bind address string into a SocketAddr.
///
/// Handles both full addresses (ip:port) and IP-only strings (adds default port).
pub fn parse_bind_address(bind: &str, default_port: u16) -> Result<SocketAddr, Box<dyn Error>> {
    match bind.parse() {
        Ok(addr) => Ok(addr),
        Err(_) => {
            let with_port = format!("{}:{}", bind, default_port);
            with_port.parse().map_err(|e| {
                Box::new(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    format!("Failed to parse bind address: {}", e),
                )) as Box<dyn Error>
            })
        }
    }
}
