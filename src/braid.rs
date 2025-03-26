// Standard Imports
use std::collections::{HashSet, HashMap};
// Custom Imports
use crate::beads::{DagBead, BeadHash};
use crate::utils::Time;

pub struct Cohort(HashSet<BeadHash>);

pub struct DagBraid {
    beads: HashSet<BeadHash>,
    tips: HashSet<BeadHash>,
    cohorts: Vec<Cohort>
}

impl DagBraid {
    pub fn new(genesis_beads: HashSet<BeadHash>) -> Self {
        DagBraid {
            beads: genesis_beads.clone(),
            tips: genesis_beads.clone(),
            cohorts: vec![Cohort(genesis_beads)]
        }
    }

    pub fn generate_from_previous_dag(previous_dag_braid: DagBraid) -> Self {
        let cohorts = previous_dag_braid.generate_tip_cohorts();
        DagBraid {
            beads: previous_dag_braid.tips.clone(),
            tips: previous_dag_braid.tips,
            cohorts
        }
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
                if cohort.0.contains(&tip) {
                    temporary_cohort.insert(tip.clone());
                }
            }

            if temporary_cohort.len() != 0 {
                cohorts.push(Cohort(temporary_cohort.clone()))
            }
        }

        cohorts
    }

    pub fn contains_bead(&self, bead_hash: BeadHash) -> bool {
        self.beads.contains(&bead_hash)
    }

    #[inline]
    fn remove_parent_beads_from_tips(&mut self, bead: &DagBead) {
        for (parent_hash, _) in &bead.bead_data.parents {
            self.tips.remove(parent_hash);
        }
    }

    pub fn add_bead(&mut self, bead: DagBead) -> AddBeadStatus {
        if bead.is_valid_bead() == false {
            return AddBeadStatus::InvalidBead;
        }

        if self.contains_bead(bead.bead_data.bead_hash) {
            return AddBeadStatus::DagAlreadyContainsBead
        }

        self.beads.insert(bead.bead_data.bead_hash);
        self.remove_parent_beads_from_tips(&bead);
        self.tips.insert(bead.bead_data.bead_hash);

        self.cohorts = self.calculate_cohorts();

        AddBeadStatus::BeadAdded
    }    
}

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded
}