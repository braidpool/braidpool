// Standard Imports
use std::cell::Cell;

// Primitives Imports
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, TxMerkleNode, Txid};
use bitcoin::hashes::{Sha256d};

// Internal Type Definitions for Clarity
type MerkleRoot = TxMerkleNode;

pub struct MerklePathProof {
    transaction_hash: Txid,
    merkle_path: Vec<TxMerkleNode>
}

impl MerklePathProof {
    pub fn calculate_corresponding_merkle_root(&self) -> MerkleRoot {
        let mut current_hash = self.transaction_hash.as_byte_array().clone();
        for merkle_node in &self.merkle_path {
            let merkle_node_as_bytes = merkle_node.as_byte_array();
            
            let mut concatenated_hashes = Vec::new();
            concatenated_hashes.extend_from_slice(&current_hash);
            concatenated_hashes.extend_from_slice(merkle_node_as_bytes);

            current_hash = Sha256d::hash(&concatenated_hashes).as_byte_array().clone();
        };

        TxMerkleNode::from_byte_array(current_hash)
    }
}

#[derive(Debug)]
pub struct MiningBlockHeader {
    pub version: BlockVersion,
    pub previous_block_hash: BlockHash,
    pub merkle_root: MerkleRoot,
    pub time: BlockTime,
    pub network_difficulty_target: CompactTarget,
    pub nonce: Cell<u32>
}

impl From<MiningBlockHeader> for BlockHeader {
    fn from(mined_header: MiningBlockHeader) -> Self {
        BlockHeader {
            version: mined_header.version,
            prev_blockhash: mined_header.previous_block_hash,
            merkle_root: mined_header.merkle_root,
            time: mined_header.time,
            bits: mined_header.network_difficulty_target,
            nonce: mined_header.nonce.get()
        }
    }
}

