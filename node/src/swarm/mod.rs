//! Swarm module for P2P networking functionality.
//!
//! This module encapsulates all libp2p swarm-related code including:
//! - Swarm construction and configuration
//! - Boot node discovery and connection
//! - Event handling and dispatch
//! - Bead processing utilities

pub mod bootstrap;
pub mod builder;
pub mod config;
pub mod handlers;
pub mod p2p_event_loop;

use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

use libp2p::PeerId;
use tokio::sync::{mpsc::Sender, RwLock};

use crate::{
    braid::Braid, db::BraidpoolDBTypes, ibd_manager::IBDCommands, peer_manager::PeerManager,
    SwarmCommand,
};

/// Shared context for swarm event handlers.
///
/// Bundles all dependencies needed by event handlers into a single struct,
/// holding lock at granular level for better lock management
pub struct SwarmContext {
    /// The shared braid DAG structure
    pub braid: Arc<RwLock<Braid>>,
    /// Channel to send database commands
    pub db_tx: Sender<BraidpoolDBTypes>,
    /// Channel to send IBD commands
    pub ibd_tx: Sender<IBDCommands>,
    /// Flag indicating if node is in Initial Block Download mode
    pub ibd_spinlock: Arc<AtomicBool>,
    /// Peer scoring and management
    pub peer_manager: Arc<RwLock<PeerManager>>,
    /// Channel to send swarm commands other than p2p
    pub swarm_cmd_tx: Sender<SwarmCommand>,
}

impl SwarmContext {
    /// Creates a new SwarmContext with all required dependencies.
    pub fn new(
        braid: Arc<RwLock<Braid>>,
        db_tx: Sender<BraidpoolDBTypes>,
        ibd_tx: Sender<IBDCommands>,
        ibd_spinlock: Arc<AtomicBool>,
        peer_manager: Arc<RwLock<PeerManager>>,
        swarm_cmd_tx: Sender<SwarmCommand>,
    ) -> Self {
        Self {
            braid,
            db_tx,
            ibd_tx,
            ibd_spinlock,
            peer_manager,
            swarm_cmd_tx,
        }
    }

    /// Check if the node is currently in IBD mode.
    #[inline]
    pub fn is_in_ibd(&self) -> bool {
        self.ibd_spinlock.load(Ordering::SeqCst)
    }

    /// Set the IBD flag.
    #[inline]
    pub fn set_ibd(&self, value: bool) {
        self.ibd_spinlock.store(value, Ordering::SeqCst);
    }

    /// Get the best peer for syncing (lowest latency).
    pub async fn get_sync_peer(&self) -> Option<PeerId> {
        {
            let peer_manager = self.peer_manager.read().await;
            peer_manager
                .get_top_k_peers_for_propagation(1)
                .into_iter()
                .next()
        }
    }
}
