use crate::bead::Bead;
use crate::utils::{BeadHash, BeadLoadError};
use ::serde::Serialize;
use bitcoin::CompactTarget;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Serialize)]

pub(crate) struct Cohort(HashSet<BeadHash>);

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}

// Type Aliases
type NumberOfBeadsUnorphaned = usize;
#[derive(Clone, Debug)]

pub struct Braid {
    pub(crate) beads: HashSet<BeadHash>,
    pub(crate) tips: HashSet<BeadHash>,
    pub(crate) cohorts: Vec<Cohort>,
    pub(crate) orphan_beads: Vec<Bead>,
    pub(crate) loaded_beads_in_memory: HashMap<BeadHash, Bead>,
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
            loaded_beads_in_memory: HashMap::new(),
            genesis_beads: genesis_beads,
        }
    }

    pub fn load_beads_in_memory(&mut self, beads: Vec<Bead>) {
        for bead in beads {
            let bead_hash = bead.block_header.block_hash();
            self.loaded_beads_in_memory.insert(bead_hash, bead);
        }
    }

    pub fn generate_from_previous_dag(previous_dag_braid: Braid) -> Self {
        let cohorts = previous_dag_braid.generate_tip_cohorts();
        Braid {
            beads: previous_dag_braid.tips.clone(),
            tips: previous_dag_braid.tips.clone(),
            cohorts,
            orphan_beads: Vec::new(),
            loaded_beads_in_memory: HashMap::new(),
            genesis_beads: previous_dag_braid.tips,
        }
    }

    pub fn add_bead(&mut self, bead: Bead) -> AddBeadStatus {
        if bead.is_valid_bead() == false {
            return AddBeadStatus::InvalidBead;
        }

        if self.contains_bead(bead.get_bead_hash()) {
            return AddBeadStatus::DagAlreadyContainsBead;
        }

        if bead.is_orphaned(self) {
            self.orphan_beads.push(bead);
            return AddBeadStatus::ParentsNotYetReceived;
        }

        // self.beads.insert(bead.bead_hash);
        self.remove_parent_beads_from_tips(&bead);
        // self.tips.insert(bead.bead_hash);

        self.cohorts = self.calculate_cohorts();
        self.update_orphan_bead_set();

        AddBeadStatus::BeadAdded
    }
}

impl Braid {
    #[inline]
    pub(crate) fn load_bead_from_hash(&self, bead_hash: BeadHash) -> Result<&Bead, BeadLoadError> {
        match self.loaded_beads_in_memory.get(&bead_hash) {
            Some(bead) => Ok(bead),
            None => Err(BeadLoadError::BeadPruned),
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
        if !bead
            .committed_metadata
            .parents
            .iter()
            .all(|p| self.beads.contains(p))
        {
            return false;
        }
        // Already seen this bead
        let bead_hash = bead.get_bead_hash();
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

    #[inline]
    fn contains_bead(&self, bead_hash: BeadHash) -> bool {
        self.beads.contains(&bead_hash)
    }

    fn is_genesis_bead(&self, bead_hash: BeadHash) -> Result<bool, BeadLoadError> {
        let bead = self.load_bead_from_memory(bead_hash)?;

        if bead.committed_metadata.parents.is_empty() {
            return Ok(true);
        };

        // We need to check whether even one of the parent beads have been pruned from memory!
        for parent_bead_hash in &bead.committed_metadata.parents {
            let parent_bead = self.load_bead_from_memory(parent_bead_hash.clone());
            if let Err(error_type) = parent_bead {
                match error_type {
                    BeadLoadError::BeadNotFound => return Ok(true),
                    _ => return Err(error_type),
                };
            }
        }

        Ok(false)
    }

    #[inline]
    fn load_bead_from_memory(&self, bead_hash: BeadHash) -> Result<&Bead, BeadLoadError> {
        // This functions returns a bead from memory! Future DB work goes in here!

        // TODO: Add in a check for whether a bead_hash is valid!

        match self.loaded_beads_in_memory.get(&bead_hash) {
            Some(bead) => Ok(bead),
            None => Err(BeadLoadError::BeadNotFound),
        }
    }

    #[inline]
    fn remove_parent_beads_from_tips(&mut self, bead: &Bead) {
        for parent_hash in &bead.committed_metadata.parents {
            self.tips.remove(parent_hash);
        }
    }

    #[inline]
    fn is_bead_orphaned(&self, bead: &Bead) -> bool {
        for parent in &bead.committed_metadata.parents {
            if self.beads.contains(parent) == false {
                return true;
            }
        }

        false
    }

    fn update_orphan_bead_set(&mut self) -> NumberOfBeadsUnorphaned {
        let old_orphan_set_length = self.orphan_beads.len();
        let old_orphan_set = std::mem::replace(&mut self.orphan_beads, Vec::new());
        for orphan_bead in old_orphan_set {
            if orphan_bead.is_genesis_bead(self) {
                self.orphan_beads.push(orphan_bead)
            }
        }

        return old_orphan_set_length - self.orphan_beads.len();
    }

    fn calculate_valid_difficulty_for_bead(&self, bead: &Bead) -> CompactTarget {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests;
