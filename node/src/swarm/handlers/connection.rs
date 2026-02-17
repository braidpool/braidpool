//! Connection establishment and closure handlers.

use std::net::IpAddr;
use std::sync::Arc;

use libp2p::{
    core::{ConnectedPoint, Multiaddr},
    swarm::ConnectionId,
    PeerId, Swarm,
};
use tokio::sync::RwLock;
use tracing::info;

use crate::{behaviour::BraidPoolBehaviour, peer_manager::PeerManager};

/// Handles a new connection being established.
pub async fn handle_connection_established(
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer_manager: &Arc<RwLock<PeerManager>>,
    peer_id: PeerId,
    endpoint: &ConnectedPoint,
) {
    let remote_addr = endpoint.get_remote_address();

    // Add to Kademlia DHT
    swarm
        .behaviour_mut()
        .kademlia
        .add_address(&peer_id, remote_addr.clone());
    info!(address = ?remote_addr, "DHT updated with peer address");

    // Add to FloodSub mesh
    swarm
        .behaviour_mut()
        .bead_announce
        .add_node_to_partial_view(peer_id);
    info!(peer = %peer_id, "Peer added to floodsub mesh");

    // Extract IP address from multiaddr
    let ip = extract_ip_from_multiaddr(remote_addr);

    // Register in peer manager
    {
        let mut peer_manager = peer_manager.write().await;
        peer_manager.add_peer(peer_id, !endpoint.is_dialer(), ip);
    }

    info!(
        peer_id = ?peer_id,
        remote_addr = ?remote_addr,
        "Connection established to peer"
    );
}

/// Handles a connection being closed.
pub async fn handle_connection_closed(
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer_manager: &Arc<RwLock<PeerManager>>,
    peer_id: PeerId,
    connection_id: ConnectionId,
    endpoint: &ConnectedPoint,
    num_established: u32,
    cause: Option<&libp2p::swarm::ConnectionError>,
) {
    let remote_addr = endpoint.get_remote_address();

    info!(
        peer = %peer_id,
        connection_id = %connection_id,
        address = %remote_addr,
        established = %num_established,
        cause = ?cause,
        "Connection closed"
    );

    // Remove from peer manager
    {
        let mut peer_manager = peer_manager.write().await;
        peer_manager.remove_peer(&peer_id);
    }

    // Remove from Kademlia DHT
    swarm
        .behaviour_mut()
        .kademlia
        .remove_address(&peer_id, remote_addr);
}

/// Extracts IP address from a multiaddr.
fn extract_ip_from_multiaddr(addr: &Multiaddr) -> Option<IpAddr> {
    addr.iter().find_map(|p| match p {
        libp2p::core::multiaddr::Protocol::Ip4(ip) => Some(IpAddr::V4(ip)),
        libp2p::core::multiaddr::Protocol::Ip6(ip) => Some(IpAddr::V6(ip)),
        _ => None,
    })
}
