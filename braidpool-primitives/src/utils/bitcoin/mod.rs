// Standard Imports
use bitcoin::merkle_tree::MerkleNode;
use std::cell::Cell;
// Primitives Imports
use bitcoin::secp256k1::hashes::hex::DisplayHex;
use bitcoin::{
    BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, Transaction, TxMerkleNode, Txid,
};

use crate::utils::test_utils::{hash_data, reverse_hex_byte_order};

// Internal Type Definitions for Clarity
type MerkleRoot = TxMerkleNode;
#[derive(Clone, Debug)]

pub struct MerklePathProof {
    pub transaction_hash: Txid,
    pub merkle_path: Vec<TxMerkleNode>,
}

impl MerklePathProof {
    pub fn calculate_corresponding_merkle_root(
        &self,
        testing_option: Option<(String, Vec<Transaction>)>,
    ) -> MerkleRoot {
        if testing_option.is_some() == true {
            let tuple_val = testing_option.unwrap();
            let default_order = tuple_val.1;
            let tx_ids = default_order.iter().map(|obj| obj.compute_txid());
            let merkel_root = TxMerkleNode::calculate_root(tx_ids);
            println!("Merkel path proof ---- {:?}", merkel_root);
            return merkel_root.unwrap();
        }
        //transactionid along with its sibling
        //taking hash and converting it to its raw bytes
        let irreversed_id = self.transaction_hash.to_string();
        let reversed_curr_tx_id = reverse_hex_byte_order(&irreversed_id);
        let mut current_hash = [0u8; 32];
        let result = hex::decode_to_slice(reversed_curr_tx_id, &mut current_hash);
        match result {
            Ok(val) => {
                println!("Decoded successfully");
            }
            Err(error) => {
                println!("{:?} this error occurred while decoding", error);
            }
        }
        //traversing its siblings
        for merkle_node in &self.merkle_path {
            //sibling byte along the merkel path
            let merkle_tx_hex_str = merkle_node.to_string();
            let curr_hash_hex_str =
                current_hash.to_hex_string(bitcoin::secp256k1::hashes::hex::Case::Lower);
            //concatanate siblings along the merkel path
            let concatanate_hash = format!("{curr_hash_hex_str}{merkle_tx_hex_str}");
            let hashed_val = hash_data(&concatanate_hash);
            hex::decode_to_slice(hashed_val, &mut current_hash)
                .expect("An error occurred while decoding");
        }
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
