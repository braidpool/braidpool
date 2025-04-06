// Standard Imports
use std::collections::HashSet;

// Bitcoin Imports
use bitcoin::{CompactTarget, Transaction};

// Custom Imports
use crate::bead::Bead;
use crate::utils::BeadHash;

// Type Definitions
#[derive(Clone, Debug)]
struct Cohort(HashSet<BeadHash>);

#[derive(Debug)]
pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}

// Type Aliases
type NumberOfBeadsUnorphaned = usize;

pub struct Braid {
    beads: HashSet<BeadHash>,
    tips: HashSet<BeadHash>,
    cohorts: Vec<Cohort>,

    orphan_beads: Vec<Bead>,

    // Database related functions!
    loaded_beads_in_memory: Vec<Bead>,
}

impl Braid {
    // All public funtions go here!
    pub fn new(genesis_beads: HashSet<BeadHash>) -> Self {
        Braid {
            beads: genesis_beads.clone(),
            tips: genesis_beads.clone(),
            cohorts: vec![Cohort(genesis_beads)],
            orphan_beads: Vec::new(),
            loaded_beads_in_memory: Vec::new(),
        }
    }

    pub fn generate_from_previous_dag(previous_dag_braid: Braid) -> Self {
        let cohorts = previous_dag_braid.generate_tip_cohorts();
        Braid {
            beads: previous_dag_braid.tips.clone(),
            tips: previous_dag_braid.tips,
            cohorts,
            orphan_beads: Vec::new(),
            loaded_beads_in_memory: Vec::new(),
        }
    }

    pub fn add_bead(
        &mut self,
        bead: Bead,
        testing_option: Option<(String, Vec<Transaction>)>,
    ) -> AddBeadStatus {
        if bead.is_valid_bead(Some(testing_option.unwrap())) == false {
            return AddBeadStatus::InvalidBead;
        }

        if bead.lesser_difficulty_target != self.calculate_valid_difficulty_for_bead(&bead) {
            return AddBeadStatus::InvalidBead;
        }

        if self.contains_bead(bead.bead_hash) {
            return AddBeadStatus::DagAlreadyContainsBead;
        }

        if self.is_bead_orphaned(&bead) {
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

    fn contains_bead(&self, bead_hash: BeadHash) -> bool {
        self.beads.contains(&bead_hash)
    }

    #[inline]
    fn remove_parent_beads_from_tips(&mut self, bead: &Bead) {
        for (parent_hash, _) in &bead.parents {
            self.tips.remove(parent_hash);
        }
    }

    #[inline]
    fn is_bead_orphaned(&self, bead: &Bead) -> bool {
        for (parent, _) in &bead.parents {
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
            if self.is_bead_orphaned(&orphan_bead) {
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