// Standard Imports
use std::cell::Cell;

// Primitives Imports
use bitcoin::hashes::Sha256d;
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, TxMerkleNode, Txid};

// Internal Type Definitions for Clarity
type MerkleRoot = TxMerkleNode;

pub struct MerklePathProof {
    pub transaction_hash: Txid,
    /// Index of the transaction in the block. Its bits give the left/right
    /// position of the running hash at each level of the merkle tree.
    /// Fixed-width so the layout is identical across platforms.
    pub transaction_index: u32,
    pub merkle_path: Vec<TxMerkleNode>,
}

impl MerklePathProof {
    pub fn calculate_corresponding_merkle_root(&self) -> MerkleRoot {
        let mut current_hash: [u8; 32] = self.transaction_hash.to_byte_array();
        let mut index = self.transaction_index;
        let mut preimage = [0u8; 64];

        for sibling in self.merkle_path.iter() {
            if index & 1 == 1 {
                // Running hash is the right child at this level.
                preimage[..32].copy_from_slice(sibling.as_byte_array());
                preimage[32..].copy_from_slice(&current_hash);
            } else {
                // Running hash is the left child at this level.
                preimage[..32].copy_from_slice(&current_hash);
                preimage[32..].copy_from_slice(sibling.as_byte_array());
            }
            current_hash = Sha256d::hash(&preimage).to_byte_array();
            index >>= 1;
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
