// Standard Imports
use std::cell::Cell;
use std::collections::HashSet;

// Custom Imports
use crate::utils::{Time, Hash};
use crate::utils::bitcoin::{BlockHash, BlockHeader, CompactTarget, MiningBlockHeader, SerializedTransaction, SerializedTransactionWithMerkleProof};

// Typedefs
type BeadHash = BlockHash;

// TODO: Add in the uncommitted metadata into the Bead Structs!

/// Refers to the final immutable beads that are added
/// into the DagBraid data structure. 
pub struct DagBead<'dag> {
    pub block_header: BlockHeader,
    pub bead_hash: BeadHash,
    pub coinbase_transaction: SerializedTransaction,
    pub payout_update_transaction: SerializedTransaction,
    
    // Committed Braidpool Metadata
    pub lesser_difficulty_target: CompactTarget,
    pub parents: HashSet<(&'dag DagBead<'dag>, Time)>,
    pub transactions: Vec<SerializedTransactionWithMerkleProof>
}

/// Refers to the bead data structure that will be used
/// to send beads to other nodes connected on the Network
pub struct NetworkBead {
    block_header: BlockHeader,
    bead_hash: BeadHash,
    coinbase_transaction: SerializedTransaction,
    payout_update_transaction: SerializedTransaction,
    
    lesser_difficulty_target: CompactTarget,
    parents: HashSet<BeadHash>,
    transactions: Vec<SerializedTransaction>
}

/// Refers to the bead that is currently being mined by a
/// Node.
pub struct MiningBead {
    block_header: MiningBlockHeader,
    coinbase_transaction: SerializedTransaction,
    payout_update_transaction: SerializedTransaction,
    
    lesser_difficulty_target: CompactTarget,
    parents: HashSet<BeadHash>,
    transactions: Vec<SerializedTransaction>
}