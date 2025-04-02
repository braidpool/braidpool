// Standard Imports
use std::collections::HashSet;

// Bitcoin primitives
use bitcoin::absolute::Time;
use bitcoin::transaction::TransactionExt;
use bitcoin::{BlockHeader, CompactTarget, Transaction};

// Custom Imports
use crate::utils::BeadHash;
use crate::utils::bitcoin::MerklePathProof;

// Type Aliases
type TransactionWithMerklePath = (Transaction, MerklePathProof);

pub struct Bead {
    pub block_header: BlockHeader,
    pub bead_hash: BeadHash,
    pub coinbase_transaction: TransactionWithMerklePath,
    pub payout_update_transaction: TransactionWithMerklePath,

    // Committed Braidpool Metadata,
    pub lesser_difficulty_target: CompactTarget,
    pub parents: HashSet<(BeadHash, Time)>,
    pub transactions: Vec<Transaction>,

    pub observed_time_at_node: Time,
}

impl Bead {
    // All public definitions go in here!
    #[inline]
    pub fn is_transaction_included_in_block(
        &self,
        transaction_with_proof: &TransactionWithMerklePath,
    ) -> bool {
        transaction_with_proof
            .1
            .calculate_corresponding_merkle_root()
            == self.block_header.merkle_root
    }

    pub fn is_valid_bead(&self) -> bool {
        // Check whether the transactions are included in the block!
        if self.is_transaction_included_in_block(&self.coinbase_transaction) == false {
            false
        } else if self.is_transaction_included_in_block(&self.payout_update_transaction) == false {
            false
        } else if self.coinbase_transaction.0.is_coinbase() == false {
            false
        } else if self.bead_hash != self.block_header.block_hash() {
            false
        } else {
            true
        }
    }

    pub fn get_coinbase_transaction(&self) -> Transaction {
        // TODO: Implement this function.
        unimplemented!()
    }

    pub fn get_payout_update_transaction(&self) -> Transaction {
        // TODO: Implement this function.
        unimplemented!()
    }
}

impl Bead {
    // All private function definitions go here!
}

#[cfg(test)]
mod tests {
    // Unit Tests for Private Functions
}
