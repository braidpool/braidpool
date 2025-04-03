#![allow(unused)]
// Standard Imports
use std::cell::RefCell;
use ::serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::net::SocketAddr;

// Bitcoin primitives
use bitcoin::Address;
use bitcoin::absolute::Time;
use bitcoin::ecdsa::Signature;
use bitcoin::p2p::Address as P2P_Address;
use bitcoin::secp256k1::PublicKey;
use bitcoin::transaction::TransactionExt;
use bitcoin::{BlockHeader, Transaction};
// Custom Imports
use crate::utils::BeadHash;
#[derive(Clone, Debug, Serialize)]

pub struct CommittedMetadata {
use crate::braid::Braid;
use crate::utils::bitcoin::MerklePathProof;
use crate::utils::{BeadHash, BeadLoadError, Children, Parents};

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
    pub transaction_cnt: u32,
    pub transactions: Vec<Transaction>,
    pub parents: HashSet<BeadHash>,
    pub payout_address: Address,
    //timestamp when the bead was created
    pub observed_time_at_node: Time,

    // Optimizations (not part of specification!)
    children: RefCell<HashSet<BeadHash>>,
    pub comm_pub_key: PublicKey,
    pub miner_ip: SocketAddr,
}
#[derive(Clone, Debug, Serialize)]

pub struct UnCommittedMetadata {
    //Uncomitted Metadata
    //timestamp when the bead was broadcasted
    pub extra_nonce: i32,
    pub broadcast_timestamp: Time,
    pub signature: Signature,
    pub parent_bead_timestamps: HashSet<Time>,
}
#[derive(Clone, Debug, Serialize)]

pub struct Bead {
    pub block_header: BlockHeader,
    pub committed_metadata: CommittedMetadata,
    pub uncommitted_metadata: UnCommittedMetadata,
}

impl Bead {
    pub fn is_valid_bead(&self) -> bool {
        // Check whether the transactions are included in the block
        true
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

        // TODO: While Implementing the DB, we also need to update the corresponding DB Entry!
    }
}

impl Bead {
    // All private function definitions go here
    //TODO : To implement a reverse mapping since we will be including the
    //consensus determining attribute in the committed portion and those which
    //will be used afterward such as in retargeting algorithms such as the parentbead_timestamps they shall be
    //included inside the uncommitted portion but the order must be same as that of the hashset of parents_bead_hashes present
    //inside the committed metadata
    pub fn reverse_mapping_parentbead_with_timestamp() {}
}

#[cfg(test)]
mod tests;
