#![allow(non_snake_case)]
use crate::bead::Bead;
use crate::braid::Braid;
use crate::edca::{FeeVerdict, FeeVerdictSource};
use crate::error::BraidError;
use crate::utils::compute_block_hash;
pub mod audit_db_handlers;
pub mod db_handlers;
pub mod init_db;
#[derive(Debug, Clone)]
pub struct BeadInsertData {
    pub bead: Bead,
    pub bead_id: usize,
    pub parent_refs: Vec<(u64, u32)>,
    /// Fee total this node verified for the bead, `None` when unverified.
    pub verified_fee_sats: Option<u64>,
}

impl BeadInsertData {
    /// Resolves a bead into a [`BeadInsertData`] using the braid's index mapping.
    ///
    /// `verdicts` supplies the fee total verified for the bead; without it the
    /// bead is stored as unverified.
    pub fn resolve(
        braid: &Braid,
        bead: &Bead,
        verdicts: Option<&(dyn FeeVerdictSource + Sync)>,
    ) -> Result<Self, BraidError> {
        let &bead_id = braid
            .bead_index_mapping
            .get(&braid.compute_bead_hash(bead))
            .ok_or(BraidError::BeadNotIndexed {
                bead: braid.compute_bead_hash(bead),
            })?;
        Ok(BeadInsertData {
            parent_refs: braid.resolve_parents(bead)?,
            bead: bead.clone(),
            bead_id,
            verified_fee_sats: verdicts.and_then(|verdicts| match verdicts.verdict(bead) {
                FeeVerdict::Verified { fee_sats } => Some(fee_sats),
                FeeVerdict::Deviated | FeeVerdict::Unknown => None,
            }),
        })
    }
    pub fn resolve_many<'a>(
        braid: &Braid,
        beads: impl IntoIterator<Item = &'a Bead>,
        verdicts: Option<&(dyn FeeVerdictSource + Sync)>,
    ) -> Result<Vec<Self>, BraidError> {
        beads
            .into_iter()
            .map(|bead| Self::resolve(braid, bead, verdicts))
            .collect()
    }
}

/// Resolves a newly-added bead and its promoted orphans against the braid index
/// and sends them to the DB handler, together with the fee totals `verdicts`
/// verified for them.
pub async fn persist_added_bead<'a>(
    braid: &Braid,
    bead: &Bead,
    promoted_orphans: impl IntoIterator<Item = &'a Bead>,
    verdicts: Option<&(dyn FeeVerdictSource + Sync)>,
    db_tx: &tokio::sync::mpsc::Sender<BraidpoolDBTypes>,
) -> Result<(), BraidError> {
    let bead_data = BeadInsertData::resolve(braid, bead, verdicts)?;
    let removed_orphans = BeadInsertData::resolve_many(braid, promoted_orphans, verdicts)?;
    if let Err(error) = db_tx
        .send(BraidpoolDBTypes::InsertTupleTypes {
            query: InsertTupleTypes::InsertBeadsBatch {
                beads: vec![bead_data],
                removed_orphans,
            },
        })
        .await
    {
        tracing::error!(err = ?error.0, "Failed to send InsertBeadsBatch to DB handler");
        return Err(BraidError::PersistenceChannelClosed {
            bead: compute_block_hash(&bead.block_header, braid.network),
        });
    }
    Ok(())
}

#[derive(Debug, Clone)]

pub enum InsertTupleTypes {
    InsertBeadsBatch {
        beads: Vec<BeadInsertData>,
        removed_orphans: Vec<BeadInsertData>,
    },
}
#[derive(Debug, Clone)]
pub enum BraidpoolDBTypes {
    InsertTupleTypes { query: InsertTupleTypes },
}
