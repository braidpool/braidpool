// Standard Imports
use std::collections::HashSet;

use bitcoin::absolute::Time;
use bitcoin::pow::CompactTargetExt;
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, Transaction, TransactionVersion, TxMerkleNode, Txid};

use crate::utils::bitcoin::MerklePathProof;
// Custom Imports
use crate::utils::BeadHash;
use crate::beads::{Bead, DagBead};

pub struct Cohort(HashSet<BeadHash>);

// Type Aliases
type NumberOfBeadsUnorphaned = usize;

// Placeholder struct (Will be replaced with appropriate implementation later!)
struct Database();
impl Database {
    pub fn fetch_bead_from_memory(&self, bead_hash: BeadHash) -> DagBead {
        // Dummy Implementation
        DagBead {
            bead_data: Bead {
                block_header: BlockHeader {
                    version: BlockVersion::ONE,
                    prev_blockhash: BlockHash::from_byte_array([0; 32]),
                    merkle_root: TxMerkleNode::from_byte_array([0; 32]),
                    time: BlockTime::from_u32(Time::MIN.to_consensus_u32()),
                    bits: CompactTarget::from_hex("0x1d00ffff").unwrap(),
                    nonce: 0
                },
                bead_hash: BeadHash::from_byte_array([0; 32]),
                coinbase_transaction: (Transaction {
                    version: TransactionVersion::ONE,
                    lock_time: bitcoin::absolute::LockTime::from_height(0).unwrap(),
                    input: Vec::new(),
                    output: Vec::new()
                }, MerklePathProof {
                    transaction_hash: Txid::from_byte_array([0; 32]),
                    merkle_path: Vec::new()
                }),
                payout_update_transaction: (Transaction {
                    version: TransactionVersion::ONE,
                    lock_time: bitcoin::absolute::LockTime::from_height(0).unwrap(),
                    input: Vec::new(),
                    output: Vec::new()
                }, MerklePathProof {
                    transaction_hash: Txid::from_byte_array([0; 32]),
                    merkle_path: Vec::new()
                }),

                lesser_difficulty_target: CompactTarget::from_hex("0x1d00ffff").unwrap(),
                parents: HashSet::new(),
                transactions: Vec::new()
            }, 
            observed_time_at_node: Time::MIN
        }
    }
}

pub struct DagBraid {
    beads: HashSet<BeadHash>,
    tips: HashSet<BeadHash>,
    cohorts: Vec<Cohort>,

    orphan_beads: Vec<DagBead>,

    // Database related functions!
    loaded_beads_in_memory: Vec<DagBead>,
    database_reference: Database
}

impl DagBraid {
    pub fn new(genesis_beads: HashSet<BeadHash>) -> Self {
        DagBraid {
            beads: genesis_beads.clone(),
            tips: genesis_beads.clone(),
            cohorts: vec![Cohort(genesis_beads)],
            orphan_beads: Vec::new(),
            loaded_beads_in_memory: Vec::new(),
            database_reference: Database()
        }
    }

    pub fn generate_from_previous_dag(previous_dag_braid: DagBraid) -> Self {
        let cohorts = previous_dag_braid.generate_tip_cohorts();
        DagBraid {
            beads: previous_dag_braid.tips.clone(),
            tips: previous_dag_braid.tips,
            cohorts,
            orphan_beads: Vec::new(),
            loaded_beads_in_memory: Vec::new(),
            database_reference: Database()
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

    pub fn contains_bead(&self, bead_hash: BeadHash) -> bool {
        self.beads.contains(&bead_hash)
    }

    #[inline]
    fn remove_parent_beads_from_tips(&mut self, bead: &DagBead) {
        for (parent_hash, _) in &bead.bead_data.parents {
            self.tips.remove(parent_hash);
        }
    }

    #[inline]
    fn is_bead_orphaned(&self, bead: &DagBead) -> bool {
        for (parent, _) in &bead.bead_data.parents {
            if self.beads.contains(parent) == false {
                return true
            }
        };

        false
    }

    fn update_orphan_bead_set(&mut self) -> NumberOfBeadsUnorphaned {
        let old_orphan_set_length = self.orphan_beads.len();
        let old_orphan_set = std::mem::replace(&mut self.orphan_beads, Vec::new());
        for orphan_bead in old_orphan_set {
            if self.is_bead_orphaned(&orphan_bead) {
                self.orphan_beads.push(orphan_bead)
            }
        };

        return old_orphan_set_length - self.orphan_beads.len();
    }

    pub fn add_bead(&mut self, bead: DagBead) -> AddBeadStatus {
        if bead.is_valid_bead() == false {
            return AddBeadStatus::InvalidBead;
        }

        if bead.bead_data.lesser_difficulty_target != self.calculate_valid_difficulty_for_bead(&bead) {
            return AddBeadStatus::InvalidBead;
        }

        if self.contains_bead(bead.bead_data.bead_hash) {
            return AddBeadStatus::DagAlreadyContainsBead
        }

        if self.is_bead_orphaned(&bead) {
            self.orphan_beads.push(bead);
            return AddBeadStatus::ParentsNotYetReceived
        }

        self.beads.insert(bead.bead_data.bead_hash);
        self.remove_parent_beads_from_tips(&bead);
        self.tips.insert(bead.bead_data.bead_hash);

        self.cohorts = self.calculate_cohorts();
        self.update_orphan_bead_set();

        AddBeadStatus::BeadAdded
    }

    fn calculate_valid_difficulty_for_bead(&self, bead: &DagBead) -> CompactTarget {
        // TODO: Implement this function!
        CompactTarget::from_hex("0x1d00ffff").unwrap()
    }
}

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived
}