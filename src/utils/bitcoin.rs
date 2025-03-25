// Custom Imports
use super::Hash;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MerkleHash {
    pub hash: Hash
}

type Byte = u8;
type Bytes = Vec<Byte>;
#[derive(Debug, Clone)]
pub struct Transaction {
    pub transaction: Bytes,
    pub merkle_proof_path: Option<Vec<MerkleHash>>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BlockHeader {
    pub version: u32,
    pub previous_block_hash: Hash,
    pub merkle_root: MerkleHash,
    pub timestamp: u32,
    pub network_difficulty_target: u32,
    pub nonce: u32
}