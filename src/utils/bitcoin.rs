// Standard Imports
use std::cell::Cell;
use transitive::Transitive;
use num_bigint::BigUint;

// Custom Imports
use super::{Hash, Bytes};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BlockTime(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Version(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Transitive)]
#[transitive(from(String, Hash))]
#[transitive(from(&str, Hash))]
#[transitive(from(BigUint, Hash))]

pub struct TransactionHash(pub Hash);

impl From<Hash> for TransactionHash {
    fn from(transaction_hash: Hash) -> Self {
        TransactionHash(transaction_hash)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Transitive)]
#[transitive(from(String, Hash))]
#[transitive(from(&str, Hash))]
#[transitive(from(BigUint, Hash))]
pub struct MerkleHash(pub Hash);

impl From<Hash> for MerkleHash {
    fn from(merkle_hash: Hash) -> Self{
        MerkleHash(merkle_hash)
    }
}

pub struct MerklePathProof {
    transaction_hash: TransactionHash,
    merkle_path: Vec<MerkleHash>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct CompactTarget(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Transitive)]
#[transitive(from(String, Hash))]
#[transitive(from(&str, Hash))]
#[transitive(from(BigUint, Hash))]
pub struct BlockHash(pub Hash);

impl From<Hash> for BlockHash {
    fn from(block_hash: Hash) -> Self {
        BlockHash(block_hash)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SerializedTransaction(Bytes);

#[derive(Debug)]
pub struct MiningBlockHeader {
    pub version: Version,
    pub previous_block_hash: Hash,
    pub merkle_root: MerkleHash,
    pub time: BlockTime,
    pub network_difficulty_target: CompactTarget,
    pub nonce: Cell<u32>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BlockHeader {
    pub version: Version,
    pub previous_block_hash: Hash,
    pub merkle_root: MerkleHash,
    pub time: BlockTime,
    pub network_difficulty_target: CompactTarget,
    pub nonce: u32
}

impl From<MiningBlockHeader> for BlockHeader {
    fn from(mined_header: MiningBlockHeader) -> Self {
        BlockHeader {
            version: mined_header.version,
            previous_block_hash: mined_header.previous_block_hash,
            merkle_root: mined_header.merkle_root,
            time: mined_header.time,
            network_difficulty_target: mined_header.network_difficulty_target,
            nonce: mined_header.nonce.get()
        }
    }
}