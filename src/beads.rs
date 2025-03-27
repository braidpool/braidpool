// Standard Imports
use std::collections::HashSet;

// Bitcoin primitives
use bitcoin::absolute::Time;
use bitcoin::{BlockHeader, CompactTarget, Transaction};

// Custom Imports
use crate::utils::bitcoin::MerklePathProof;
use crate::utils::BeadHash;

// TODO: Add in the uncommitted metadata into the Bead Structs!

type TransactionWithMerklePath = (Transaction, MerklePathProof);
/// Refers to the final immutable beads that are added
/// into the DagBraid data structure. 
pub struct DagBead {
    pub bead_data: Bead,
    pub observed_time_at_node: Time
}

pub struct Bead {
    pub block_header: BlockHeader,
    pub bead_hash: BeadHash,
    pub coinbase_transaction: TransactionWithMerklePath,
    pub payout_update_transaction: TransactionWithMerklePath,

    // Committed Braidpool Metadata,
    pub lesser_difficulty_target: CompactTarget,
    pub parents: HashSet<(BeadHash, Time)>,
    pub transactions: Vec<Transaction>
}

impl DagBead {
    pub fn is_valid_bead(&self) -> bool {
        self.bead_data.is_valid_bead()
    }
}

impl Bead {
    pub fn is_valid_bead(&self) -> bool {
        // TODO: Implement Checks
        true
    }
}