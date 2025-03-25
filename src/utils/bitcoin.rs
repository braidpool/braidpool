// Standard Imports
use std::cell::Cell;

// Custom Imports
use super::{Hash, Bytes};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BlockTime(u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Version(u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct MerkleHash(Hash);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct CompactTarget(u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BlockHash(Hash);

#[derive(Debug, Clone)]
pub struct Transaction {
    pub serialized_transaction: Bytes,
    pub merkle_proof_path: Option<Vec<MerkleHash>>
}

#[derive(Debug)]
pub struct MiningBlockHeader {
    pub version: Version,
    pub previous_block_hash: Hash,
    pub merkle_root: MerkleHash,
    pub time: BlockTime,
    pub network_difficulty_target: CompactTarget,
    pub nonce: Cell<u32>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BlockHeader {
    pub version: Version,
    pub previous_block_hash: Hash,
    pub merkle_root: MerkleHash,
    pub time: BlockTime,
    pub network_difficulty_target: CompactTarget,
    pub nonce: u32
}