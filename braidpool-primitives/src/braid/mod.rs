// Standard Imports
use std::collections::{HashMap, HashSet};

// Bitcoin Imports
use bitcoin::CompactTarget;

// Custom Imports
use crate::bead::Bead;
use crate::utils::{BeadHash, BeadLoadError};

// Type Definitions
struct Cohort(HashSet<BeadHash>);

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}

// Type Aliases
type NumberOfBeadsUnorphaned = usize;

pub struct Braid {
    pub(crate) beads: HashSet<BeadHash>,
    pub(crate) tips: HashSet<BeadHash>,
    pub(crate) cohorts: Vec<Cohort>,

    pub(crate) orphan_beads: Vec<Bead>,

    // Database related functions!
    pub(crate) loaded_beads_in_memory: HashMap<BeadHash, Bead>,

    // Optimizations (not part of specification!)
    pub(crate) genesis_beads: HashSet<BeadHash>
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
            genesis_beads: genesis_beads
        }
    }

    pub fn load_beads_in_memory(&mut self, beads: Vec<Bead>) {
        for bead in beads {
            let bead_hash = bead.bead_hash;
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
            genesis_beads: previous_dag_braid.tips
        }
    }

    pub fn add_bead(&mut self, bead: Bead) -> AddBeadStatus {
        if bead.is_valid_bead() == false {
            return AddBeadStatus::InvalidBead;
        }

        if bead.lesser_difficulty_target != self.calculate_valid_difficulty_for_bead(&bead) {
            return AddBeadStatus::InvalidBead;
        }

        if self.contains_bead(bead.bead_hash) {
            return AddBeadStatus::DagAlreadyContainsBead;
        }

        if bead.is_orphaned(self) {
            self.orphan_beads.push(bead);
            return AddBeadStatus::ParentsNotYetReceived;
        }

        self.beads.insert(bead.bead_hash);
        self.remove_parent_beads_from_tips(&bead);
        self.tips.insert(bead.bead_hash);

        self.cohorts = self.calculate_cohorts();
        self.update_orphan_bead_set();

        AddBeadStatus::BeadAdded
    }
}

impl Braid {
    // All pub(crate) functions go here!
    #[inline]
    pub(crate) fn load_bead_from_hash(&self, bead_hash: BeadHash) -> Result<&Bead, BeadLoadError> {
        // This functions returns a bead from memory! Future DB work goes in here!

        // TODO: Add in a check for whether a bead_hash is valid!

        match self.loaded_beads_in_memory.get(&bead_hash) {
            Some(bead) => Ok(bead),
            None => Err(BeadLoadError::BeadPruned),
        }
    }
}

impl Braid {
    // All private functions go here!
    fn get_parents(&self) -> HashMap<BeadHash, HashSet<BeadHash>> {
        let mut parents = HashMap::new();
        for beadhash in self.beads.iter() {
            let bead = match self.loaded_beads_in_memory.get(beadhash) {
                Some(bead) => bead,
                None => continue, // TODO: Load from the database
            };
            let mut this_parents = HashSet::new();
            for (parent_hash, _) in &bead.parents {
                this_parents.insert(parent_hash.clone());
            }
            parents.insert(beadhash.clone(), this_parents);
        }
        parents
    }

    fn get_children(&self) -> HashMap<BeadHash, HashSet<BeadHash>> {
        let mut children = HashMap::new();
        for (beadhash, parents) in self.get_parents() {
            for parent in parents {
                children
                    .entry(parent.clone())
                    .or_insert_with(HashSet::new)
                    .insert(beadhash.clone());
            }
            children
                .entry(beadhash.clone())
                .or_insert_with(HashSet::new);
        }
        children
    }

    fn get_tips(&self) -> HashSet<BeadHash> {
        let mut tips = HashSet::new();
        let children = self.get_children();
        for (beadhash, children_set) in children {
            if children_set.is_empty() {
                tips.insert(beadhash.clone());
            }
        }
        tips
    }

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

    fn contains_bead(&self, bead_hash: BeadHash) -> bool {
        self.beads.contains(&bead_hash)
    }

    #[inline]
    fn remove_parent_beads_from_tips(&mut self, bead: &Bead) {
        for (parent_hash, _) in &bead.parents {
            self.tips.remove(parent_hash);
        }
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
