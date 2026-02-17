//! Identify protocol event handlers.

use libp2p::{identify, PeerId};
use tracing::{debug, error, info};

use crate::behaviour::{BEAD_ANNOUNCE_PROTOCOL, KADPROTOCOLNAME};

/// Handles identify info sent to a peer.
pub fn handle_sent(peer_id: PeerId) {
    debug!(peer = ?peer_id, "Sent identify info");
}

/// Handles identify info received from a peer.
pub fn handle_received(peer_id: PeerId, info: identify::Info) {
    info!(
        peer = ?peer_id,
        address_count = %info.listen_addrs.len(),
        "Received listen addresses"
    );

    // Check if peer supports Kademlia
    if info.protocols.iter().any(|p| *p == KADPROTOCOLNAME) {
        for addr in &info.listen_addrs {
            info!(address = %addr, "Received address via identify");
        }
    } else {
        info!(peer = ?peer_id, "Peer does not support Kademlia");
    }

    // Check if peer supports FloodSub
    if !info.protocols.iter().any(|p| *p == BEAD_ANNOUNCE_PROTOCOL) {
        info!(
            peer_address = ?info.observed_addr,
            "Peer does not support floodsub"
        );
    }

    debug!(info = ?info, "Received peer info");
}

/// Handles identify protocol errors.
pub fn handle_error<E: std::fmt::Debug>(peer_id: PeerId, error: E) {
    error!(
        peer = %peer_id,
        error = ?error,
        "Identify event error"
    );
}
