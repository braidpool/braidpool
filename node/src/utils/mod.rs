// Bitcoin Imports
use crate::{
    bead::Bead,
    committed_metadata::{CommittedMetadata, TimeVec},
    uncommitted_metadata::UnCommittedMetadata,
};
use ::bitcoin::BlockHash;
use bitcoin::{
    absolute::MedianTimePast as Time, ecdsa::Signature, BlockHeader, BlockTime, BlockVersion,
    CompactTarget, EcdsaSighashType, TxMerkleNode,
};
// Standard Imports

pub mod test_utils;

// External Type Aliases
pub type BeadHash = BlockHash;
pub type Byte = u8;
pub type Bytes = Vec<Byte>;

// Internal Type Aliases
#[allow(dead_code)]
pub(crate) type Relatives = HashSet<BeadHash>;

// Error Definitions
use std::{collections::HashSet, str::FromStr};

pub(crate) fn hashset_to_vec_deterministic(hashset: &HashSet<BeadHash>) -> Vec<BeadHash> {
    let mut vec: Vec<BeadHash> = hashset.iter().cloned().collect();
    vec.sort();
    vec
}

pub(crate) fn vec_to_hashset(vec: Vec<BeadHash>) -> HashSet<BeadHash> {
    vec.iter().cloned().collect()
}

pub(crate) fn retrieve_bead(_beadhash: BeadHash) -> Option<Bead> {
    // This function is a placeholder for the actual retrieval logic.
    // In a real implementation, this would fetch the bead from a database or other storage.
    None
}

// Helper function to create test beads
pub fn create_test_bead(nonce: u32, prev_hash: Option<BlockHash>) -> Bead {
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let time_hash_set = TimeVec(Vec::new());
    let mut parent_hash_set: HashSet<BlockHash> = HashSet::new();
    if let Some(hash) = prev_hash {
        parent_hash_set.insert(hash);
    }
    let weak_target = CompactTarget::from_consensus(32);
    let min_target = CompactTarget::from_consensus(1);
    let time_val = Time::from_consensus(1653195600).unwrap();
    let test_committed_metadata: CommittedMetadata = CommittedMetadata {
        comm_pub_key: public_key,
        min_target: min_target,
        miner_ip: "".to_string(),
        transactions: vec![],
        parents: parent_hash_set,
        parent_bead_timestamps: time_hash_set,
        payout_address: String::from(""),
        start_timestamp: time_val,
        weak_target: weak_target,
    };
    let extra_nonce = 42;
    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let test_uncommitted_metadata = UnCommittedMetadata {
        broadcast_timestamp: time_val,
        extra_nonce: extra_nonce,
        signature: sig,
    };
    let test_bytes: [u8; 32] = [0u8; 32];
    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: prev_hash.unwrap_or(BlockHash::from_byte_array(test_bytes)),
        bits: CompactTarget::from_consensus(32),
        nonce: nonce,
        time: BlockTime::from_u32(8328429),
        merkle_root: TxMerkleNode::from_byte_array(test_bytes),
    };
    Bead {
        block_header: test_block_header,
        committed_metadata: test_committed_metadata,
        uncommitted_metadata: test_uncommitted_metadata,
    }
}
