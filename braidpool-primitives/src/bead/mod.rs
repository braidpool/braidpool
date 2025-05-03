#![allow(unused)]
use bitcoin::io::{self, Write};
// Standard Imports
use ::serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::net::SocketAddr;

// Bitcoin primitives
use bitcoin::Address;
use bitcoin::absolute::Time;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::encode::serialize;
use bitcoin::ecdsa::Signature;
use bitcoin::p2p::Address as P2P_Address;
use bitcoin::secp256k1::PublicKey;
use bitcoin::transaction::TransactionExt;
use bitcoin::{BlockHeader, Transaction};
// Custom Imports
use crate::utils::BeadHash;

/// Wrapper type for HashSet<BeadHash> to allow custom trait implementations.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct BeadHashSet(pub HashSet<BeadHash>);

impl Encodable for BeadHashSet {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += (self.0.len() as u64).consensus_encode(w)?;
        for item in self.0.iter() {
            len += item.consensus_encode(w)?;
        }
        Ok(len)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct TimeHashSet(pub HashSet<Time>);

impl Encodable for TimeHashSet {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        // Encode the length for deterministic encoding
        len += (self.0.len() as u64).consensus_encode(w)?;
        for time in &self.0 {
            len += time.to_consensus_u32().consensus_encode(w)?;
        }
        Ok(len)
    }
}

/// Wrapper type for SocketAddr to allow custom trait implementations.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct SerializableSocketAddr(pub SocketAddr);

impl Encodable for SerializableSocketAddr {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let (address, port) = match self.0 {
            SocketAddr::V4(addr) => (addr.ip().to_ipv6_mapped().segments(), addr.port()),
            SocketAddr::V6(addr) => (addr.ip().segments(), addr.port()),
        };
        let mut len = 0;
        len += address.consensus_encode(w)?;
        len += port.consensus_encode(w)?;
        Ok(len)
    }
}

#[derive(Clone, Debug)]

pub struct CommittedMetadata {
    // Committed Braidpool Metadata,
    pub transaction_cnt: u32,
    pub transactions: Vec<Transaction>,
    pub parents: BeadHashSet,
    pub payout_address: P2P_Address,
    //timestamp when the bead was created
    pub observed_time_at_node: Time,
    pub comm_pub_key: PublicKey,
    pub miner_ip: SerializableSocketAddr,
}

impl Encodable for CommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.transaction_cnt.consensus_encode(w)?;
        len += self.transactions.consensus_encode(w)?;
        len += self.parents.consensus_encode(w)?;
        len += self.payout_address.consensus_encode(w)?;
        len += self
            .observed_time_at_node
            .to_consensus_u32()
            .consensus_encode(w)?;
        let pubkey_bytes = self.comm_pub_key.serialize();
        len += pubkey_bytes.consensus_encode(w)?;
        len += self.miner_ip.consensus_encode(w)?;
        Ok(len)
    }
}

#[derive(Clone, Debug, Serialize)]

pub struct UnCommittedMetadata {
    //Uncomitted Metadata
    //timestamp when the bead was broadcasted
    pub extra_nonce: i32,
    pub broadcast_timestamp: Time,
    pub signature: Signature,
    pub parent_bead_timestamps: TimeHashSet,
}

impl Encodable for UnCommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.extra_nonce.consensus_encode(w)?;
        len += self
            .broadcast_timestamp
            .to_consensus_u32()
            .consensus_encode(w)?;
        len += self.signature.to_string().consensus_encode(w)?;
        len += self.parent_bead_timestamps.consensus_encode(w)?;
        Ok(len)
    }
}

#[derive(Clone, Debug)]

pub struct Bead {
    pub block_header: BlockHeader,
    pub committed_metadata: CommittedMetadata,
    pub uncommitted_metadata: UnCommittedMetadata,
}

impl Encodable for Bead {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.block_header.consensus_encode(w)?;
        len += self.committed_metadata.consensus_encode(w)?;
        len += self.uncommitted_metadata.consensus_encode(w)?;
        Ok(len)
    }
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

    // #[inline]
    // pub fn is_parent_of(&self, child_bead_hash: BeadHash) -> bool {
    //     self.children.borrow().contains(&child_bead_hash)
    // }

    pub fn is_genesis_bead(&self, braid: &Braid) -> bool {
        if self.committed_metadata.parents.0.is_empty() {
            return true;
        };

        // We need to check whether even one of the parent beads have been pruned from memory!
        for parent_bead_hash in self.committed_metadata.parents.0.iter() {
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
        for parent in self.committed_metadata.parents.0.iter() {
            if braid.beads.contains(parent) == false {
                return true;
            }
        }

        false
    }

    #[inline]
    pub fn get_parents(&self) -> Parents {
        // The bead might get pruned later, so we can't give a shared reference!
        self.committed_metadata.parents.0.clone()
    }

    // #[inline]
    // pub fn get_children(&self) -> Children {
    //     self.children.borrow().iter().cloned().collect()
    // }
}

impl Bead {
    // All pub(crate) function definitions go here!
    #[inline]
    pub(crate) fn add_child(&self, child_bead_hash: BeadHash) {
        // TODO: While Implementing the DB, we also need to update the corresponding DB Entry!
        // self.children.borrow_mut().insert(child_bead_hash);
        unimplemented!();
    }

    pub fn get_bead_hash(&self) -> BlockHash {
        let serialized_bead = serialize(self);
        let mut serialized_bytes = [0u8; 32];
        hex::decode_to_slice(serialized_bead, &mut serialized_bytes).unwrap();
        BlockHash::from_byte_array(serialized_bytes)
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
