// Standard Imports
use std::collections::HashSet;

// Bitcoin Imports
use bitcoin::{CompactTarget, Transaction};

// Custom Imports
use crate::beads::Bead;
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
mod tests {
    use super::Cohort;
    use super::{BeadHash, HashSet};
    use crate::braid::Braid;
    use crate::utils::test_utils::create_test_bead;
    use ::bitcoin::absolute::Time;
    use ::bitcoin::BlockHash;
    #[test]
    fn add_bead_test() {
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        let prev_block_bytes_str =
            "00000000000000000001061c8069cd7b85f966f80d0b375c4f0c31e7827ff119";
        let mut prev_bytes = [0u8; 32];
        //not reversing as in explorer can do if you want.
        hex::decode_to_slice(prev_block_bytes_str, &mut prev_bytes).unwrap();
        //input tx paying UTXOs to the current one for constructing dummy transaction.
        //random payout txin from mainnet for testing purposes
        let payout_txin = "30c239f3ae062c5f1151476005fd0057adfa6922de1b38d0f11eb657a8157b30";
        let mut payout_tx_bytes = [0u8; 32];
        let result = hex::decode_to_slice(payout_txin, &mut payout_tx_bytes);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        //transaction bytes that will include the txins for the transactions to be added inside
        //the bead apart from coinbase_tx and payout_tx
        let mut tx_included_in_bead: Vec<[u8; 32]> = Vec::new();
        let txs = [
            "b983ae54c70f58afb9f5b09b44b89131a6019d56e2b4fa2de0d6864781e0103e",
            "9ed532e904f4ddfc506cd0ba59a098b5fb805bd5a5e80ab89f8a6e655c9a6240",
        ];

        for tx in txs {
            let mut curr_bytes = [0u8; 32];
            let result = hex::decode_to_slice(tx, &mut curr_bytes);
            match result {
                Ok(val) => {
                    println!("Successfully decoded {:?}", val);
                    tx_included_in_bead.push(curr_bytes);
                }
                Err(e) => {
                    println!(
                        "{:?} this error occurred while decoding the corresponding bytes",
                        e
                    );
                }
            }
        }


        let test_dag_bead_1 = create_test_bead(
            2,
            prev_bytes,
            1653195600,
            486604799,
            1,
            payout_tx_bytes,
            123456,
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
            tx_included_in_bead,
            2345678,
            2345456,
        );
        genesis_beads.insert(test_dag_bead_1.bead_hash);
        let mut test_braid = Braid::new(genesis_beads);
        let reference = test_dag_bead_1.clone();
        let mut all_txs = Vec::new();
        all_txs.push(reference.coinbase_transaction.0);
        let tx_referenced = reference.transactions.clone();
        for tx in tx_referenced {
            all_txs.push(tx);
        }
        all_txs.push(reference.payout_update_transaction.0);
        test_braid.add_bead(test_dag_bead_1, Some((String::from("testing"), all_txs)));
        assert_eq!(test_braid.beads.contains(&reference.bead_hash), true);
    }

    #[test]
    fn test_update_orphans() {
        //--------------------------------1st test Bead----------------------------------------------------//
        let prev_block_bytes_str_1 =
            "00000000000000000002a7d5f0b2a6e4ff8d5e2a3c47f5c9b4f8e7d1c2b3a9e7";
        let mut prev_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(prev_block_bytes_str_1, &mut prev_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        let payout_txin_1 = "450c309b70fb3f71b63b10ce60af17499bd21b1db39aa47b19bf22166ee67144";
        let mut payout_tx_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(payout_txin_1, &mut payout_tx_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        let mut tx_included_in_bead_1: Vec<[u8; 32]> = Vec::new();
        let txs_1 = [
            "c9d1b7e4f5a3d2c6b8e0f5a7d3c9b1e6f4a7b2e0c5d1b8e6f4a3d7b9c2e5f0d8",
            "e6f4a3d7b9c2e5f0d8c9d1b7e4f5a3d2c6b8e0f5a7d3c9b1e6f4a7b2e0c5d1b8",
        ];

        for tx in txs_1 {
            let mut curr_bytes_1 = [0u8; 32];
            let result = hex::decode_to_slice(tx, &mut curr_bytes_1);
            match result {
                Ok(val) => {
                    println!("Successfully decoded {:?}", val);
                    tx_included_in_bead_1.push(curr_bytes_1);
                }
                Err(e) => {
                    println!(
                        "{:?} this error occurred while decoding the corresponding bytes",
                        e
                    );
                }
            }
        }

        //--------------------------------2nd test bead----------------------------------------------------//
        let prev_block_bytes_str_2 =
            "00000000000000000000efc4be188e9d2053681791a5c53b07ecfe8ba00f8464";
        let mut prev_bytes_2 = [0u8; 32];
        let result = hex::decode_to_slice(prev_block_bytes_str_2, &mut prev_bytes_2);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }

        let payout_txin_2 = "450c309b70fb3f71b63b10ce60af17499bd21b1db39aa47b19bf22166ee67144";
        let mut payout_tx_bytes_2 = [0u8; 32];
        let result = hex::decode_to_slice(payout_txin_2, &mut payout_tx_bytes_2);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        let mut tx_included_in_bead_2: Vec<[u8; 32]> = Vec::new();
        let txs_2 = [
            "c8f0a4e7b3d5c1f9a6c2d5f9e7b4d1c7f3a5e9b2d6c8f0a4e7b3d5c1f9a6c2d5",
            "f3a5e9b2d6c8f0a4e7b3d5c1f9a6c2d5f9e7b4d1c7f3a5e9b2d6c8f0a4e7b3d5",
        ];

        for tx in txs_2 {
            let mut curr_bytes_2 = [0u8; 32];
            let result = hex::decode_to_slice(tx, &mut curr_bytes_2);
            match result {
                Ok(val) => {
                    println!("Successfully decoded {:?}", val);
                    tx_included_in_bead_2.push(curr_bytes_2);
                }
                Err(e) => {
                    println!(
                        "{:?} this error occurred while decoding the corresponding bytes",
                        e
                    );
                }
            }
        }

        //-------------------------------------3rd test bead --------------------------------------------
        let prev_block_bytes_str_3 =
            "00000000000000000000efc4be188e9d2053681791a5c53b07ecfe8ba00f8464";
        let mut prev_bytes_3 = [0u8; 32];
        let result = hex::decode_to_slice(prev_block_bytes_str_3, &mut prev_bytes_3);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }

        let payout_txin_3 = " 450c309b70fb3f71b63b10ce60af17499bd21b1db39aa47b19bf22166ee67144 ";
        let mut payout_tx_bytes_3 = [0u8; 32];
        let result = hex::decode_to_slice(payout_txin_3, &mut payout_tx_bytes_3);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }

        let mut tx_included_in_bead_3: Vec<[u8; 32]> = Vec::new();
        let txs_3 = [
            "a5e7f3c9e2a7d5f3b1c6d8e4a9b2f5c7d3e6a0b4f9d1c8a5e7f3c9e2a7d5f3b1",
            "c6d8e4a9b2f5c7d3e6a0b4f9d1c8a5e7f3c9e2a7d5f3b1c6d8e4a9b2f5c7d3e6",
        ];

        for tx in txs_3 {
            let mut curr_bytes_3 = [0u8; 32];
            let result = hex::decode_to_slice(tx, &mut curr_bytes_3);
            match result {
                Ok(val) => {
                    println!("Successfully decoded {:?}", val);
                    tx_included_in_bead_3.push(curr_bytes_3);
                }
                Err(e) => {
                    println!(
                        "{:?} this error occurred while decoding the corresponding bytes",
                        e
                    );
                }
            }
        }

        // bead 1 and bead 2 will be parents for bead 3
        //bead 1 and bead 2 will be genesis beads for this test braid  and bead 3 will
        //be child
        let test_dag_bead_1 = create_test_bead(
            2,
            prev_bytes_1,
            1653195601,
            486604790,
            1,
            payout_tx_bytes_1,
            123455,
            vec![],
            tx_included_in_bead_1,
            2345678,
            2345457,
        );
        let test_dag_bead_2 = create_test_bead(
            2,
            prev_bytes_2,
            1653195602,
            486604791,
            1,
            payout_tx_bytes_2,
            123456,
            vec![],
            tx_included_in_bead_2,
            2345678,
            2345457,
        );
        let child_bead_1 = create_test_bead(
            2,
            prev_bytes_3,
            1653195603,
            486604792,
            1,
            payout_tx_bytes_3,
            123457,
            vec![
                (
                    test_dag_bead_1.bead_hash,
                    Time::from_consensus(1690000000).expect("Invalid  time provided"),
                ),
                (
                    test_dag_bead_2.bead_hash,
                    Time::from_consensus(1690000000).expect("Invalid time provided"),
                ),
            ],
            tx_included_in_bead_3,
            2345678,
            2345458,
        );
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();

        genesis_beads.insert(test_dag_bead_1.bead_hash);
        genesis_beads.insert(test_dag_bead_2.bead_hash);

        let mut test_braid = Braid::new(genesis_beads);
        let child_bead_reference = child_bead_1.clone();
        let mut all_txs = Vec::new();
        all_txs.push(child_bead_reference.coinbase_transaction.0);
        for tx in child_bead_reference.transactions {
            all_txs.push(tx);
        }
        all_txs.push(child_bead_reference.payout_update_transaction.0);
        test_braid.add_bead(child_bead_1, Some((String::from("testing"), all_txs)));
        assert_eq!(test_braid.update_orphan_bead_set(), 0);
    }
    #[test]
    fn test_orphan_bead() {
        let prev_block_bytes_str_1 =
            "00000000000000000002a7d5f0b2a6e4ff8d5e2a3c47f5c9b4f8e7d1c2b3a9e7";
        let mut prev_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(prev_block_bytes_str_1, &mut prev_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }

        let payout_txin_1 = "450c309b70fb3f71b63b10ce60af17499bd21b1db39aa47b19bf22166ee67144";
        let mut payout_tx_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(payout_txin_1, &mut payout_tx_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        let mut tx_included_in_bead_1: Vec<[u8; 32]> = Vec::new();
        let txs_1 = [
            "c9d1b7e4f5a3d2c6b8e0f5a7d3c9b1e6f4a7b2e0c5d1b8e6f4a3d7b9c2e5f0d8",
            "e6f4a3d7b9c2e5f0d8c9d1b7e4f5a3d2c6b8e0f5a7d3c9b1e6f4a7b2e0c5d1b8",
        ];

        for tx in txs_1 {
            let mut curr_bytes_1 = [0u8; 32];
            let result = hex::decode_to_slice(tx, &mut curr_bytes_1);
            match result {
                Ok(val) => {
                    println!("Successfully decoded {:?}", val);
                    tx_included_in_bead_1.push(curr_bytes_1);
                }
                Err(e) => {
                    println!(
                        "{:?} this error occurred while decoding the corresponding bytes",
                        e
                    );
                }
            }
        }

        let test_dag_bead = create_test_bead(
            2,
            prev_bytes_1,
            1653195601,
            486604711,
            1,
            payout_tx_bytes_1,
            123456,
            vec![],
            tx_included_in_bead_1,
            2345678,
            2345456,
        );
        //genesis bead for initalization with random 32 byte hash
        let bytes: [u8; 32] = [0; 32];
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        genesis_beads.insert(BlockHash::from_byte_array(bytes));
        let mut test_braid = Braid::new(genesis_beads);
        let referenced_bead = test_dag_bead.clone();

        assert_eq!(test_braid.is_bead_orphaned(&referenced_bead), false);
    }
    #[test]
    fn test_remove_parents() {
        let prev_block_bytes_str_1 =
            "00000000000000000002a7d5f0b2a6e4ff8d5e2a3c47f5c9b4f8e7d1c2b3a9e7";
        let mut prev_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(prev_block_bytes_str_1, &mut prev_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        let payout_txin_1 = "450c309b70fb3f71b63b10ce60af17499bd21b1db39aa47b19bf22166ee67144";
        let mut payout_tx_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(payout_txin_1, &mut payout_tx_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
        let mut tx_included_in_bead_1: Vec<[u8; 32]> = Vec::new();
        let txs_1 = [
            "c9d1b7e4f5a3d2c6b8e0f5a7d3c9b1e6f4a7b2e0c5d1b8e6f4a3d7b9c2e5f0d8",
            "e6f4a3d7b9c2e5f0d8c9d1b7e4f5a3d2c6b8e0f5a7d3c9b1e6f4a7b2e0c5d1b8",
        ];

        for tx in txs_1 {
            let mut curr_bytes_1 = [0u8; 32];
            let result = hex::decode_to_slice(tx, &mut curr_bytes_1);
            match result {
                Ok(val) => {
                    println!("Successfully decoded {:?}", val);
                    tx_included_in_bead_1.push(curr_bytes_1);
                }
                Err(e) => {
                    println!(
                        "{:?} this error occurred while decoding the corresponding bytes",
                        e
                    );
                }
            }
        }

        let test_dag_bead = create_test_bead(
            2,
            prev_bytes_1,
            1653195601,
            486604790,
            1,
            payout_tx_bytes_1,
            123455,
            vec![],
            tx_included_in_bead_1,
            12345679,
            2345468,
        );
        let bytes: [u8; 32] = [0; 32];
        let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
        genesis_beads.insert(BlockHash::from_byte_array(bytes));
        let mut test_braid = Braid::new(genesis_beads);

        let referenced_val = test_dag_bead.clone();
        let ref_2 = referenced_val.clone();
        let mut all_txs = Vec::new();
        all_txs.push(referenced_val.coinbase_transaction.0);
        for tx in referenced_val.transactions {
            all_txs.push(tx);
        }
        all_txs.push(referenced_val.payout_update_transaction.0);
        test_braid.add_bead(test_dag_bead, Some((String::from("testing"), all_txs)));
        test_braid.remove_parent_beads_from_tips(&ref_2);

        let parents = ref_2.parents;
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
