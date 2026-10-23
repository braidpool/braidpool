use libp2p::PeerId;
use tokio::sync::RwLockWriteGuard;
use tracing::{debug, error};

use crate::{
    bead::Bead,
    braid::{AddBeadStatus, Braid},
    db::persist_added_bead,
    swarm::SwarmContext,
};

/// Result of processing an incoming bead.
#[derive(Debug)]
pub struct BeadProcessingResult {
    /// The status returned by braid.extend()
    pub status: AddBeadStatus,
    /// Whether the bead was successfully persisted to DB
    pub persisted: bool,
}

/// Processes an incoming bead by extending the braid and persisting to DB.
///
/// This is the central bead processing function that handles:
/// - Extending the braid with the new bead
/// - Persisting the bead along with any orphans it promoted
///
/// # Arguments
/// * `ctx` - The swarm context containing shared state
/// * `braid_guard` - Write lock on the braid (caller must acquire)
/// * `bead` - The bead to process
/// * `source` - The peer that sent the bead
///
/// # Returns
/// The processing result including status and persistence state
pub async fn process_incoming_bead(
    ctx: &SwarmContext,
    braid_guard: &mut RwLockWriteGuard<'_, Braid>,
    bead: &Bead,
    source: PeerId,
) -> BeadProcessingResult {
    let status = braid_guard.extend(bead);

    let persisted = match &status {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            let bead_hash = braid_guard.compute_bead_hash(bead);
            match persist_added_bead(braid_guard, bead, promoted_orphans.iter(), &ctx.db_tx).await {
                Ok(()) => {
                    debug!(bead_hash = ?bead_hash, source = ?source, "Bead persisted to database");
                    true
                }
                Err(e) => {
                    error!(bead_hash = ?bead_hash, source = ?source, error = %e, "Failed to persist bead");
                    false
                }
            }
        }
        // Invalid, orphaned or duplicate beads are not persisted here
        _ => false,
    };

    BeadProcessingResult { status, persisted }
}
