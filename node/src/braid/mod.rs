use crate::bead::Bead;
use crate::utils::BeadHash;
use ::serde::Serialize;
use std::collections::HashSet;

#[derive(Clone, Debug, Serialize)]

pub(crate) struct Cohort(HashSet<BeadHash>);

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}

#[derive(Clone, Debug)]

pub struct Braid {
    pub(crate) beads: HashSet<BeadHash>,
    pub(crate) tips: HashSet<BeadHash>,
    pub(crate) cohorts: Vec<Cohort>,
    pub(crate) orphan_beads: Vec<Bead>,
    pub(crate) genesis_beads: HashSet<BeadHash>,
}

impl Braid {
    // All public funtions go here!
    pub fn new(genesis_beads: HashSet<BeadHash>) -> Self {
        Braid {
            beads: genesis_beads.clone(),
            tips: genesis_beads.clone(),
            cohorts: vec![Cohort(genesis_beads.clone())],
            orphan_beads: Vec::new(),
            genesis_beads: genesis_beads,
        }
    }

    pub fn add_bead(&mut self, bead: Bead) -> AddBeadStatus {
        if self.beads.contains(&bead.block_header.block_hash()) {
            return AddBeadStatus::DagAlreadyContainsBead;
        }

        self.cohorts = self.calculate_cohorts();

        AddBeadStatus::BeadAdded
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
        if !bead
            .committed_metadata
            .parents
            .iter()
            .all(|p| self.beads.contains(p))
        {
            return false;
        }
        // Already seen this bead
        let bead_hash = bead.block_header.block_hash();
        if self.beads.contains(&bead_hash) {
            return false;
        }

        // Insert bead hash into beads set
        self.beads.insert(bead_hash);

        // Remove parents from tips if present
        for parent in &bead.committed_metadata.parents {
            self.tips.remove(parent);
        }
        // Add bead hash to tips
        self.tips.insert(bead_hash);

        // Find earliest parent of bead in cohorts and nuke all cohorts after that
        let mut found_parents = HashSet::new();
        let mut dangling = HashSet::new();
        dangling.insert(bead_hash);

        // We'll collect the indices to remove from cohorts
        let mut remove_after = None;
        for (i, cohort) in self.cohorts.iter().enumerate().rev() {
            // Find which parents are in this cohort
            for parent in &bead.committed_metadata.parents {
                if cohort.0.contains(parent) {
                    found_parents.insert(*parent);
                }
            }
            // Add all bead hashes in this cohort to dangling
            for h in &cohort.0 {
                dangling.insert(*h);
            }
            if found_parents.len() == bead.committed_metadata.parents.len() {
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

    // All private functions go here!
    fn calculate_cohorts(&self) -> Vec<Cohort> {
        // TODO: Implement the cohorts calculating function!
        vec![Cohort(HashSet::new())]
    }

    fn generate_tip_cohorts(&self) -> Vec<Cohort> {
        let mut cohorts = Vec::new();
        let tips = self.tips.clone();

        let mut temporary_cohort = HashSet::new();
        for cohort in self.cohorts.iter().rev() {
            temporary_cohort.clear();
            for tip in tips.iter() {
                if cohort.0.contains(tip) {
                    temporary_cohort.insert(tip.clone());
                }
            }

            if temporary_cohort.len() != 0 {
                cohorts.push(Cohort(temporary_cohort.clone()))
            }
        }

        cohorts
    }
}

#[cfg(test)]
mod tests;
