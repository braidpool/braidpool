// Standard Imports
use std::cell::Cell;

// Primitives Imports
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, TxMerkleNode, Txid};


// Internal Type Definitions for Clarity
type MerkleRoot = TxMerkleNode;

pub struct MerklePathProof {
    transaction_hash: Txid,
    merkle_path: Vec<TxMerkleNode>
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

