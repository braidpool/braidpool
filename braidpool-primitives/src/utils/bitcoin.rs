// Standard Imports
use std::cell::Cell;

// Primitives Imports
use bitcoin::hashes::Sha256d;
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, TxMerkleNode, Txid};

// Internal Type Definitions for Clarity
type MerkleRoot = TxMerkleNode;

pub struct MerklePathProof {
    pub transaction_hash: Txid,
    pub is_right_leaf: bool,
    pub merkle_path: Vec<TxMerkleNode>,
}

impl MerklePathProof {
    // All public functions go here!
    pub fn calculate_corresponding_merkle_root(&self) -> MerkleRoot {
        // Handle left and right leaf situations!
        let hashing_order = self.get_merkle_hashing_order();
        let mut concatenated_hashes: Vec<u8> = Vec::new();
        for hash in hashing_order.iter() {
            concatenated_hashes.extend_from_slice(hash);
        }

        let calculated_merkle_root = Sha256d::hash(&concatenated_hashes);
        TxMerkleNode::from_byte_array(calculated_merkle_root.to_byte_array())
    }
}

impl MerklePathProof {
    // All private functions go here!
    fn get_merkle_hashing_order(&self) -> Vec<[u8; 32]> {
        let mut hashing_order: Vec<[u8; 32]> = Vec::new();
        let index_for_starting_the_copy: usize;
        if self.is_right_leaf {
            hashing_order.push(self.merkle_path[0].as_byte_array().clone());
            hashing_order.push(self.transaction_hash.as_byte_array().clone());
            index_for_starting_the_copy = 1;
        } else {
            hashing_order.push(self.transaction_hash.as_byte_array().clone());
            index_for_starting_the_copy = 0;
        };

        for index in index_for_starting_the_copy..self.merkle_path.len() {
            hashing_order.push(self.merkle_path[index].as_byte_array().clone());
        }

        hashing_order
    }
}

#[derive(Debug)]
pub struct MiningBlockHeader {
    pub version: BlockVersion,
    pub previous_block_hash: BlockHash,
    pub merkle_root: MerkleRoot,
    pub time: BlockTime,
    pub network_difficulty_target: CompactTarget,
    pub nonce: Cell<u32>,
}

impl From<MiningBlockHeader> for BlockHeader {
    fn from(mined_header: MiningBlockHeader) -> Self {
        BlockHeader {
            version: mined_header.version,
            prev_blockhash: mined_header.previous_block_hash,
            merkle_root: mined_header.merkle_root,
            time: mined_header.time,
            bits: mined_header.network_difficulty_target,
            nonce: mined_header.nonce.get(),
        }
    }
}
