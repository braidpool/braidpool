// Standard Imports
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, DefaultHasher, Hasher};
use std::cell::{Cell, RefCell};

// Bitcoin primitives
use bitcoin::absolute::Time;
use bitcoin::transaction::TransactionExt;
use bitcoin::{BlockHeader, CompactTarget, Transaction};

// Custom Imports
use crate::utils::{BeadHash, BeadLoadError, Children, Parents};
use crate::utils::bitcoin::MerklePathProof;
use crate::braid::Braid;

// Type Aliases
type TransactionWithMerklePath = (Transaction, MerklePathProof);

pub struct Bead {
    pub block_header: BlockHeader,
    pub bead_hash: BeadHash,
    pub coinbase_transaction: TransactionWithMerklePath,
    pub payout_update_transaction: TransactionWithMerklePath,

    // Committed Braidpool Metadata,
    pub lesser_difficulty_target: CompactTarget,
    pub parents: HashMap<BeadHash, Time>,
    pub transactions: Vec<Transaction>,

    pub observed_time_at_node: Time,

    // Optimizations (not part of specification!)
    pub(crate) children: RefCell<HashSet<BeadHash>>,
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

    #[inline]
    pub fn is_parent_of(&self, child_bead_hash: BeadHash) -> bool {
        self.children.borrow().contains(&child_bead_hash)
    }

    pub fn is_genesis_bead(&self, braid: &Braid) -> bool {
        if self.parents.is_empty() {
            return true;
        };

        // We need to check whether even one of the parent beads have been pruned from memory!
        for (parent_bead_hash, _) in self.parents.iter() {
            let parent_bead = braid.load_bead_from_hash(*parent_bead_hash);
            if let Err(error_type) = parent_bead {
                match error_type {
                    BeadLoadError::BeadPruned => return true,
                    _ => panic!("Fatal Error Detected!"),
                };
            }
        }

        false
    }

    #[inline]
    pub fn is_orphaned(&self, braid: &Braid) -> bool {
        for (parent, _) in self.parents.iter() {
            if braid.beads.contains(parent) == false {
                return true;
            }
        }

        false
    }

    #[inline]
    pub fn get_parents(&self) -> Parents {
        // The bead might get pruned later, so we can't give a shared reference!
        self.parents.keys().cloned().collect()
    }

    #[inline]
    pub fn get_children(&self) -> Children {
        self.children.borrow().iter().cloned().collect()
    }

}

impl Bead {
    // All pub(crate) function definitions go here!
    #[inline]
    pub(crate) fn add_child(&self, child_bead_hash: BeadHash) {
        self.children.borrow_mut().insert(child_bead_hash);
    }
}

impl Bead {
    // All private function definitions go here!
}

#[cfg(test)]
mod tests;
