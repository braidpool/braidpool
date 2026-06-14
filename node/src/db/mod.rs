#![allow(non_snake_case)]
use crate::bead::Bead;
use crate::braid::Braid;
use crate::error::BraidError;
pub mod db_handlers;
pub mod init_db;
#[derive(Debug, Clone)]
pub struct BeadInsertData {
    pub bead: Bead,
    pub bead_id: usize,
    pub parent_refs: Vec<(u64, u32)>,
}

impl BeadInsertData {
    /// Resolves a bead into a [`BeadInsertData`] using the braid's index mapping.
    pub fn resolve(braid: &Braid, bead: &Bead) -> Result<Self, BraidError> {
        let &bead_id = braid
            .bead_index_mapping
            .get(&bead.block_header.block_hash())
            .ok_or(BraidError::BeadNotIndexed {
                bead: bead.block_header.block_hash(),
            })?;
        Ok(BeadInsertData {
            parent_refs: braid.resolve_parents(bead)?,
            bead: bead.clone(),
            bead_id,
        })
    }
    pub fn resolve_many<'a>(
        braid: &Braid,
        beads: impl IntoIterator<Item = &'a Bead>,
    ) -> Result<Vec<Self>, BraidError> {
        beads
            .into_iter()
            .map(|bead| Self::resolve(braid, bead))
            .collect()
    }
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
