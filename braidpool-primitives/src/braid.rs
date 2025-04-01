// Standard Imports
use std::collections::HashSet;

// Bitcoin Imports
use bitcoin::CompactTarget;

// Custom Imports
use crate::beads::Bead;
use crate::utils::BeadHash;

// Type Definitions
#[derive(Clone, Debug)]
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
mod tests {
    use super::Cohort;
    use super::{BeadHash, HashSet};
    use crate::braid::Braid;
    use crate::utils::test_utils::create_test_bead;
    use ::bitcoin::absolute::Time;
    use ::bitcoin::BlockHash;

    #[test]
    fn test_update_orphans() {
        let test_dag_bead_1 = create_test_bead(
            2,
            [0x00; 32],
            [
                0xf3, 0xb8, 0x76, 0x2e, 0x7c, 0x1b, 0xd6, 0x47, 0xf1, 0xf6, 0x9d, 0x2a, 0x7f, 0x9c,
                0x85, 0xf0, 0xb2, 0x5e, 0x64, 0x69, 0xf1, 0x07, 0xd2, 0x31, 0xdf, 0xf4, 0x5c, 0x47,
                0x1f, 0x88, 0x94, 0x58,
            ],
            1653195600,
            486604799,
            0,
            [0x00; 32],
            [0xbb; 32],
            [0xbb; 32],
            4040404,
            vec![
                (
                    BeadHash::from_byte_array([0x01; 32]),
                    Time::from_consensus(1690000000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x02; 32]),
                    Time::from_consensus(1690001000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x03; 32]),
                    Time::from_consensus(1690002000).expect("invalid time value"),
                ),
            ],
            vec![[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]],
            436864982,
            [0x00; 32],
            1653195600,
        );
        let test_dag_bead_2 = create_test_bead(
            2,
            [0x00; 32],
            [
                0xf3, 0xb8, 0x76, 0x2e, 0x7c, 0x1b, 0xd6, 0x47, 0xf1, 0xf6, 0x9d, 0x2a, 0x7f, 0x9c,
                0x85, 0xf0, 0xb2, 0x5e, 0x64, 0x69, 0xf1, 0x07, 0xd2, 0x31, 0xdf, 0xf4, 0x5c, 0x47,
                0x1f, 0x88, 0x94, 0x58,
            ],
            1653195600,
            486604799,
            0,
            [0x00; 32],
            [0xbb; 32],
            [0xbb; 32],
            4040404,
            vec![
                (
                    BeadHash::from_byte_array([0x01; 32]),
                    Time::from_consensus(1690000000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x02; 32]),
                    Time::from_consensus(1690001000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x03; 32]),
                    Time::from_consensus(1690002000).expect("invalid time value"),
                ),
            ],
            vec![[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]],
            436864982,
            [0x00; 32],
            1653195600,
        );
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        let child_bead_1 = create_test_bead(
            2,
            [0x00; 32],
            [
                0xf3, 0xb8, 0x76, 0x2e, 0x7c, 0x1b, 0xd6, 0x47, 0xf1, 0xf6, 0x9d, 0x2a, 0x7f, 0x9c,
                0x85, 0xf0, 0xb2, 0x5e, 0x64, 0x69, 0xf1, 0x07, 0xd2, 0x31, 0xdf, 0xf4, 0x5c, 0x47,
                0x1f, 0x88, 0x94, 0x58,
            ],
            1653195600,
            486604799,
            0,
            [0x00; 32],
            [0xbb; 32],
            [0xbb; 32],
            4040404,
            vec![
                (
                    BeadHash::from_byte_array([0x01; 32]),
                    Time::from_consensus(1690000000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x02; 32]),
                    Time::from_consensus(1690001000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x03; 32]),
                    Time::from_consensus(1690002000).expect("invalid time value"),
                ),
            ],
            vec![[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]],
            436864982,
            [0x00; 32],
            1653195600,
        );

        genesis_beads.insert(test_dag_bead_1.bead_hash);
        genesis_beads.insert(test_dag_bead_2.bead_hash);

        let mut test_braid = Braid::new(genesis_beads);

        test_braid.add_bead(test_dag_bead_1);
        test_braid.add_bead(test_dag_bead_2);
        test_braid.add_bead(child_bead_1);

        assert_eq!(test_braid.update_orphan_bead_set(), 2);
    }
    #[test]
    fn test_orphan_bead() {
        let test_dag_bead = create_test_bead(
            2,
            [0x00; 32],
            [
                0xf3, 0xb8, 0x76, 0x2e, 0x7c, 0x1b, 0xd6, 0x47, 0xf1, 0xf6, 0x9d, 0x2a, 0x7f, 0x9c,
                0x85, 0xf0, 0xb2, 0x5e, 0x64, 0x69, 0xf1, 0x07, 0xd2, 0x31, 0xdf, 0xf4, 0x5c, 0x47,
                0x1f, 0x88, 0x94, 0x58,
            ],
            1653195600,
            486604799,
            0,
            [0x00; 32],
            [0xbb; 32],
            [0xbb; 32],
            4040404,
            vec![
                (
                    BeadHash::from_byte_array([0x01; 32]),
                    Time::from_consensus(1690000000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x02; 32]),
                    Time::from_consensus(1690001000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x03; 32]),
                    Time::from_consensus(1690002000).expect("invalid time value"),
                ),
            ], // parents
            vec![[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]],
            436864982,
            [0x00; 32],
            1653195600,
        );
        let bytes: [u8; 32] = [0; 32];
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        genesis_beads.insert(BlockHash::from_byte_array(bytes));
        let mut test_braid = Braid::new(genesis_beads);
        let referenced_bead = test_dag_bead.clone();
        test_braid.add_bead(test_dag_bead);

        assert_eq!(test_braid.is_bead_orphaned(&referenced_bead), false);
    }
    #[test]
    fn test_remove_parents() {
        let test_dag_bead = create_test_bead(
            2,
            [0x00; 32],
            [
                0xf3, 0xb8, 0x76, 0x2e, 0x7c, 0x1b, 0xd6, 0x47, 0xf1, 0xf6, 0x9d, 0x2a, 0x7f, 0x9c,
                0x85, 0xf0, 0xb2, 0x5e, 0x64, 0x69, 0xf1, 0x07, 0xd2, 0x31, 0xdf, 0xf4, 0x5c, 0x47,
                0x1f, 0x88, 0x94, 0x58,
            ],
            1653195600,
            486604799,
            0,
            [0x00; 32],
            [0xbb; 32],
            [0xbb; 32],
            4040404,
            vec![
                (
                    BeadHash::from_byte_array([0x01; 32]),
                    Time::from_consensus(1690000000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x02; 32]),
                    Time::from_consensus(1690001000).expect("invalid time value"),
                ),
                (
                    BeadHash::from_byte_array([0x03; 32]),
                    Time::from_consensus(1690002000).expect("invalid time value"),
                ),
            ], // parents
            vec![[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]],
            436864982,
            [0x00; 32],
            1653195600,
        );
        let bytes: [u8; 32] = [0; 32];
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        genesis_beads.insert(BlockHash::from_byte_array(bytes));
        let mut test_braid = Braid::new(genesis_beads);

        let referenced_val = test_dag_bead.clone();
        test_braid.add_bead(test_dag_bead);
        test_braid.remove_parent_beads_from_tips(&referenced_val);

        let parents = referenced_val.parents;
        for parent in parents {
            assert_eq!(test_braid.tips.contains(&parent.0), false);
        }
    }

    #[test]
    fn test_bead_cohort_1() {
        let bytes: [u8; 32] = [0; 32];
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        let reference = genesis_beads.clone();
        genesis_beads.insert(BlockHash::from_byte_array(bytes));
        let test_braid = Braid::new(genesis_beads);
        let computed_tip_cohorts = test_braid.generate_tip_cohorts();
        let mut expected_tip_cohorts = Vec::new();
        expected_tip_cohorts.push(Cohort(reference));
        assert_eq!(expected_tip_cohorts.len(), computed_tip_cohorts.len());
        for index in 0..computed_tip_cohorts.len() {
            let expected_cohort = expected_tip_cohorts[index].clone();
            let computed_cohort = expected_tip_cohorts[index].clone();

            for cohort_element in computed_cohort.0 {
                assert_eq!(expected_cohort.0.contains(&cohort_element), true);
            }
        }
    }
}
