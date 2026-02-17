//! Ping protocol event handlers.

use std::sync::Arc;
use std::time::Duration;

use libp2p::PeerId;
use tokio::sync::RwLock;
use tracing::{info, warn};

use crate::peer_manager::PeerManager;

/// Handles successful ping responses.
pub async fn handle_ping_success(
    peer: PeerId,
    latency: Duration,
    peer_manager: &Arc<RwLock<PeerManager>>,
) {
    info!(
        peer = %peer,
        latency_ms = %latency.as_millis(),
        "Ping"
    );
    let mut peer_manager = peer_manager.write().await;
    peer_manager.update_latency(&peer, latency);
}

/// Handles ping failures.
pub fn handle_ping_failure(peer: PeerId, error: libp2p::ping::Failure) {
    warn!(
        peer = %peer,
        error = %error,
        "Ping failed"
    );
}
