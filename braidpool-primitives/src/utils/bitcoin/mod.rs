// Standard Imports
use std::cell::Cell;

// Primitives Imports
use bitcoin::hashes::Sha256d;
use bitcoin::hex::DisplayHex;
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, TxMerkleNode, Txid};

// Internal Type Definitions for Clarity
type MerkleRoot = TxMerkleNode;
#[derive(Debug, Clone)]
pub struct MerklePathProof {
    pub transaction_hash: Txid,
    pub is_right_leaf: bool,
    pub merkle_path: Vec<(TxMerkleNode, String)>,
}

impl MerklePathProof {
    // All public functions go here!
    pub fn calculate_corresponding_merkle_root(&self) -> MerkleRoot {
        let hashing_order = self.get_merkle_hashing_order();
        let mut concatenated_hashes: Vec<u8> = Vec::new();
        concatenated_hashes.extend_from_slice(&hashing_order[0].0);
        concatenated_hashes.extend_from_slice(&hashing_order[1].0);
        let mut hashed_bytes = Sha256d::hash(&concatenated_hashes).to_byte_array();
        for index in 2..hashing_order.len() {
            let parent_hash = hashed_bytes.to_hex_string(bitcoin::hex::Case::Lower);
            let current_sibling = hashing_order[index]
                .0
                .to_hex_string(bitcoin::hex::Case::Lower);
            let curr_sibling_position = hashing_order[index].1.clone();
            let mut com = String::from("");
            //If the sibling hash if R i.e. lying in some right subtree then order must be swapped before combining
            //Since the position of sibling is already known the parent hash will always be present in the opposite branched subtree
            if curr_sibling_position == "L" {
                com = format!("{}{}", current_sibling, parent_hash);
            } else if curr_sibling_position == "R" {
                com = format!("{}{}", parent_hash, current_sibling);
            }
            let mut com_bytes = [0u8; 64];
            hex::decode_to_slice(com, &mut com_bytes)
                .expect("An error occurred while decoding the corresponding String");
            let hash_com = Sha256d::hash(&com_bytes);
            hashed_bytes = hash_com.clone().to_byte_array();
        }

        return TxMerkleNode::from_byte_array(hashed_bytes);
    }
}

impl MerklePathProof {
    // All private functions go here!
    fn get_merkle_hashing_order(&self) -> Vec<([u8; 32], String)> {
        //Hashing order containing the relative position for each of the merkel node
        //present in the merkel path of the corresponding transaction which is to be
        //validated
        let mut hashing_order: Vec<([u8; 32], String)> = Vec::new();
        let index_for_starting_the_copy: usize;
        if self.is_right_leaf {
            hashing_order.push((
                self.merkle_path[0].0.as_byte_array().clone(),
                self.merkle_path[0].clone().1,
            ));
            hashing_order.push((
                self.transaction_hash.as_byte_array().clone(),
                String::from("R"),
            ));
            index_for_starting_the_copy = 1;
        } else {
            hashing_order.push((
                self.transaction_hash.as_byte_array().clone(),
                String::from("L"),
            ));
            index_for_starting_the_copy = 0;
        };

        for index in index_for_starting_the_copy..self.merkle_path.len() {
            hashing_order.push((
                self.merkle_path[index].0.as_byte_array().clone(),
                self.merkle_path[index].clone().1,
            ));
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

#[cfg(test)]
mod tests;
