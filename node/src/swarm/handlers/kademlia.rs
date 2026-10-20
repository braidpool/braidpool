//! Kademlia DHT event handlers.

use libp2p::kad;
use tracing::{error, info};

/// Handles Kademlia routing table updates.
pub fn handle_routing_updated(
    peer: libp2p::PeerId,
    is_new_peer: bool,
    addresses: kad::Addresses,
    bucket_range: (libp2p::kad::KBucketDistance, libp2p::kad::KBucketDistance),
    old_peer: Option<libp2p::PeerId>,
) {
    info!(
        peer = %peer,
        is_new = %is_new_peer,
        addresses = ?addresses,
        bucket = ?bucket_range,
        old_peer = ?old_peer,
        "DHT routing updated"
    );
}

/// Handles Kademlia outbound query progress.
pub fn handle_outbound_query(result: kad::QueryResult) {
    match result {
        kad::QueryResult::GetClosestPeers(Ok(ok)) => {
            info!(
                peers = ?ok.peers,
                peer_count = %ok.peers.len(),
                "Got closest peers"
            );
        }
        kad::QueryResult::GetClosestPeers(Err(err)) => {
            error!(error = %err, "Failed to get closest peers");
        }
        kad::QueryResult::Bootstrap(Ok(kad::BootstrapOk { peer, .. })) => {
            info!(peer = ?peer, "Bootstrap discovered new peer");
        }
        other => {
            info!(result = ?other, "Other DHT query result");
        }
    }
}
