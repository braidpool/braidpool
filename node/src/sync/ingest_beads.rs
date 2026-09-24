use crate::bead::Bead;
use crate::braid::{AddBeadStatus, Braid};
use crate::db::{BeadInsertData, BraidpoolDBTypes, InsertTupleTypes};
use crate::debug;
use crate::error::BraidError;

/// Beads are resolved into [`BeadInsertData`] without re-referring to braid
/// for additional [`PeerManager`] updates such as peer_score.
#[derive(Debug, Default, Clone)]
pub struct IngestOutcome {
    /// Beads newly added to the braid, resolved for persistence being deterministic in nature.
    pub beads_to_persist: Vec<BeadInsertData>,
    /// Orphans promoted into the DAG by this batch order will remain
    /// according to deterministic order of parents being resolved.
    pub promoted_orphans: Vec<BeadInsertData>,
    /// Count of beads the braid rejected as invalid (for peer penalisation).
    /// however even if a single bead is rejected then it can be either already present
    /// or it can be non-extendable as being orphan bead any other reason should suffice
    /// for an error.
    pub invalid: usize,
    /// Count of beads newly added (for peer reward).
    pub added: usize,
}

impl IngestOutcome {
    /// Build the batch DB insert command for the persisted beads .
    pub fn into_db_command(self) -> Option<BraidpoolDBTypes> {
        if self.beads_to_persist.is_empty() {
            return None;
        }
        Some(BraidpoolDBTypes::InsertTupleTypes {
            query: InsertTupleTypes::InsertBeadsBatch {
                beads: self.beads_to_persist,
                removed_orphans: self.promoted_orphans,
            },
        })
    }
}

/// Extend `braid` with a batch of `beads` during IBD, collecting what to persist
/// and the per-batch scoring counts for updating the `PeerManager` followed by
/// batched insertion into db instead of single insertion that will be formed as
/// and intermediate state in [`IngestOutcome`].
pub fn ingest_beads(braid: &mut Braid, beads: &[Bead]) -> Result<IngestOutcome, BraidError> {
    let mut outcome = IngestOutcome::default();
    for bead in beads {
        match braid.extend(bead) {
            AddBeadStatus::BeadAdded { promoted_orphans } => {
                outcome.added += 1;
                // Resolve against the braid now, while it is borrowable and the
                // bead is freshly indexed.
                outcome
                    .beads_to_persist
                    .push(BeadInsertData::resolve(braid, bead)?);
                outcome
                    .promoted_orphans
                    .extend(BeadInsertData::resolve_many(braid, &promoted_orphans)?);
            }
            AddBeadStatus::InvalidBead => outcome.invalid += 1,
            AddBeadStatus::DagAlreadyContainsBead => {
                debug!("Received a bead already present in DAG.");
            }
            AddBeadStatus::ParentsNotYetReceived => {
                debug!("Received an orphan bead.");
            }
        }
    }
    Ok(outcome)
}
