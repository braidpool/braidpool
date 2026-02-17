use libp2p::PeerId;
use tokio::sync::RwLockWriteGuard;
use tracing::{debug, error};

use crate::{
    bead::Bead,
    braid::{AddBeadStatus, Braid},
    db::{db_handlers::prepare_bead_tuple_data, BraidpoolDBTypes, InsertTupleTypes},
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
/// - Preparing tuple data for DB insertion
/// - Sending the bead to the database
/// - Updating peer scores
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

    match &status {
        AddBeadStatus::BeadAdded => {
            let bead_hash = bead.block_header.block_hash();

            // Get the bead ID from the mapping
            let bead_id = match braid_guard.bead_index_mapping.get(&bead_hash) {
                Some(id) => *id,
                None => {
                    error!(
                        bead_hash = ?bead_hash,
                        "Bead ID not found in index mapping after insertion"
                    );
                    return BeadProcessingResult {
                        status,
                        persisted: false,
                    };
                }
            };

            // Prepare tuple data for database
            let (txs_json, relative_json, parent_timestamp_json) = match prepare_bead_tuple_data(
                &braid_guard.beads,
                &braid_guard.bead_index_mapping,
                bead,
            ) {
                Ok(tuples) => tuples,
                Err(e) => {
                    error!(
                        bead_hash = ?bead_hash,
                        error = ?e,
                        "Failed to prepare bead tuple data"
                    );
                    return BeadProcessingResult {
                        status,
                        persisted: false,
                    };
                }
            };

            // Send to db handler
            let persisted = match ctx
                .db_tx
                .send(BraidpoolDBTypes::InsertTupleTypes {
                    query: InsertTupleTypes::InsertBeadSequentially {
                        bead_to_insert: bead.clone(),
                        txs_json,
                        relative_json,
                        parent_timestamp_json,
                        bead_id,
                    },
                })
                .await
            {
                Ok(_) => {
                    debug!(
                        bead_hash = ?bead_hash,
                        source = ?source,
                        "Bead persisted to database"
                    );
                    true
                }
                Err(e) => {
                    error!(
                        bead_hash = ?bead_hash,
                        source = ?source,
                        error = ?e.0,
                        "Failed to send bead to database"
                    );
                    false
                }
            };

            BeadProcessingResult { status, persisted }
        }
        AddBeadStatus::InvalidBead => {
            // Peer sent invalid bead penalize peer
            BeadProcessingResult {
                status,
                persisted: false,
            }
        }
        AddBeadStatus::ParentsNotYetReceived => {
            // Request parents
            BeadProcessingResult {
                status,
                persisted: false,
            }
        }
        AddBeadStatus::DagAlreadyContainsBead => {
            // Duplicate bead
            BeadProcessingResult {
                status,
                persisted: false,
            }
        }
    }
}
