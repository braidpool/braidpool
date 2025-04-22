#![allow(unused)]
// Standard Imports
use ::serde::{Deserialize, Serialize};
use std::collections::HashSet;
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
    // Committed Braidpool Metadata,
    pub transaction_cnt: u32,
    pub transactions: Vec<Transaction>,
    pub parents: HashSet<BeadHash>,
    pub payout_address: Address,
    //timestamp when the bead was created
    pub observed_time_at_node: Time,
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
