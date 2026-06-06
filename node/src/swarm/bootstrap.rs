//! Boot node connection and network bootstrapping.

use libp2p::{core::multiaddr::Multiaddr, floodsub::Topic, kad::Mode, Swarm};
use tracing::{error, info};

use crate::behaviour::BraidPoolBehaviour;

use super::config::{parse_boot_addr, parse_boot_nodes};

/// Sets up the swarm with boot nodes and starts listening.
pub fn setup_and_bootstrap(
    swarm: &mut Swarm<BraidPoolBehaviour>,
    listen_addr: Multiaddr,
    topic: Topic,
) -> Result<(), Box<dyn std::error::Error>> {
    // Subscribe to the braidpool topic
    swarm.behaviour_mut().bead_announce.subscribe(topic);

    // Set Kademlia to server mode for DHT participation
    swarm.behaviour_mut().kademlia.set_mode(Some(Mode::Server));

    // Start listening
    swarm.listen_on(listen_addr.clone())?;

    // Add boot nodes to DHT
    let boot_nodes = parse_boot_nodes();
    for (peer_id, addr) in &boot_nodes {
        swarm
            .behaviour_mut()
            .kademlia
            .add_address(peer_id, addr.clone());
    }
    info!(boot_node_count = %boot_nodes.len(), "Boot nodes added to DHT");

    // Dial primary boot node
    let boot_addr =
        parse_boot_addr().map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidInput, e))?;
    swarm.dial(boot_addr.clone())?;
    info!(address = %boot_addr, "Dialed boot node");

    Ok(())
}

/// Dials additional nodes specified via CLI.
pub fn dial_additional_nodes(swarm: &mut Swarm<BraidPoolBehaviour>, nodes: &[String]) {
    for node in nodes {
        let node_multiaddr: Multiaddr = match node.parse() {
            Ok(addr) => addr,
            Err(e) => {
                error!(node = %node, error = %e, "Failed to parse multiaddr, skipping");
                continue;
            }
        };

        match swarm.dial(node_multiaddr.clone()) {
            Ok(_) => {
                info!(address = %node_multiaddr, "Dialed peer node");
            }
            Err(e) => {
                error!(address = %node_multiaddr, error = %e, "Failed to dial peer node");
            }
        }
    }
}
