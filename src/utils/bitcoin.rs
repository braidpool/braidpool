// Standard Imports
use std::cell::Cell;

// Custom Imports
use super::{Hash, Bytes};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BlockTime(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Version(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct MerkleHash(pub Hash);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct CompactTarget(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BlockHash(pub Hash);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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