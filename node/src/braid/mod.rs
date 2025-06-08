use crate::bead::Bead;
use crate::utils::retrieve_bead;
use ::serde::Serialize;
use std::collections::HashSet;

#[derive(Clone, Debug, Serialize)]

pub(crate) struct Cohort(HashSet<usize>);

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}

#[derive(Clone, Debug)]

pub struct Braid {
    pub(crate) beads: Vec<Bead>,
    pub(crate) tips: HashSet<usize>,
    pub(crate) cohorts: Vec<Cohort>,
    pub(crate) orphan_beads: Vec<usize>,
    pub(crate) genesis_beads: HashSet<usize>,
}

impl Braid {
    // All public funtions go here!
    pub fn new(genesis_beads: HashSet<Bead>) -> Self {
        let mut beads = Vec::new();
        let mut bead_indices = HashSet::new();

        for (index, bead) in genesis_beads.into_iter().enumerate() {
            beads.push(bead);
            bead_indices.insert(index);
        }

        Braid {
            beads,
            tips: bead_indices.clone(),
            cohorts: vec![Cohort(bead_indices.clone())],
            orphan_beads: Vec::new(),
            genesis_beads: bead_indices,
        }
    }
}

impl Braid {
    /// Attempts to extend the braid with the given bead.
    /// Returns true if the bead successfully extended the braid, false otherwise.
    fn extend(&mut self, bead: &Bead) -> bool {
        // No parents: bad block
        if bead.committed_metadata.parents.is_empty() {
            return false;
        }
        // Don't have all parents
        for parent_hash in &bead.committed_metadata.parents {
            // Check if we already have this parent in our beads
            let parent_exists = self
                .beads
                .iter()
                .any(|b| b.block_header.block_hash() == *parent_hash);

            if !parent_exists {
                // Try to retrieve the parent using magic_retrieve
                if let Some(retrieved_bead) = retrieve_bead(*parent_hash) {
                    self.beads.push(retrieved_bead);
                } else {
                    // Parent not found and can't be retrieved
                    return false;
                }
            }
        }
        // Already seen this bead
        let bead_hash = bead.block_header.block_hash();
        if self
            .beads
            .iter()
            .any(|b| b.block_header.block_hash() == bead_hash)
        {
            return false;
        }

        // Insert bead into beads vector
        self.beads.push(bead.clone());

        // Remove parents from tips if present
        for parent_hash in &bead.committed_metadata.parents {
            // Find the index of the parent bead
            if let Some(parent_index) = self
                .beads
                .iter()
                .position(|b| b.block_header.block_hash() == *parent_hash)
            {
                self.tips.remove(&parent_index);
            }
        }

        // Add the new bead's index to tips
        let new_bead_index = self.beads.len() - 1;
        self.tips.insert(new_bead_index);

        // Find earliest parent of bead in cohorts and nuke all cohorts after that
        let mut found_parent_indices = HashSet::new();
        let mut dangling = HashSet::new();
        dangling.insert(new_bead_index);

        // We'll collect the indices to remove from cohorts
        let mut remove_after = None;
        for (i, cohort) in self.cohorts.iter().enumerate().rev() {
            // Find which parent indices are in this cohort
            for parent_hash in &bead.committed_metadata.parents {
                if let Some(parent_index) = self
                    .beads
                    .iter()
                    .position(|b| b.block_header.block_hash() == *parent_hash)
                {
                    if cohort.0.contains(&parent_index) {
                        found_parent_indices.insert(parent_index);
                    }
                }
            }
            // Add all bead indices in this cohort to dangling
            for idx in &cohort.0 {
                dangling.insert(*idx);
            }
            if found_parent_indices.len() == bead.committed_metadata.parents.len() {
                remove_after = Some(i + 1);
                break;
            }
        }
        // Remove all cohorts after the found index
        if let Some(idx) = remove_after {
            self.cohorts.truncate(idx);
        } else {
            self.cohorts.clear();
        }

        // Construct a sub-braid from dangling and compute any new cohorts
        // Here, we just create a new cohort with dangling beads
        if !dangling.is_empty() {
            self.cohorts.push(Cohort(dangling));
        }

        true
    }
}

#[cfg(test)]
mod tests;
