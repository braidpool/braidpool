// Standard Imports
use std::cell::Cell;
use std::collections::HashSet;

// Custom Imports
use crate::utils::{Time, Hash};
use crate::utils::bitcoin::{Transaction, MiningBlockHeader, BlockHeader, CompactTarget, BlockHash};

// Typedefs
type BeadHash = BlockHash;

// TODO: Add in the uncommitted metadata into the Bead Structs!

/// Refers to the final immutable beads that are added
/// into the DagBraid data structure. 
pub struct DagBead<'a> {
    block_header: BlockHeader,
    bead_hash: BeadHash,
    coinbase_transaction: Transaction,
    payout_update_transaction: Transaction,
    
    // Committed Braidpool Metadata
    lesser_difficulty_target: CompactTarget,
    parents: HashSet<(&'a DagBead<'a>, Time)>
}

/// Refers to the bead data structure that will be used
/// to send beads to other nodes connected on the Network
#[derive(Debug, Clone)]
pub struct NetworkBead {
    block_header: BlockHeader,
    bead_hash: BeadHash,
    coinbase_transaction: Transaction,
    payout_update_transaction: Transaction,
    
    lesser_difficulty_target: CompactTarget,
    parents: HashSet<BeadHash>
}

/// Refers to the bead that is currently being mined by a
/// Node.
pub struct MiningBead {
    block_header: MiningBlockHeader,
    coinbase_transaction: Transaction,
    payout_update_transaction: Transaction,
    
    lesser_difficulty_target: CompactTarget,
    parents: HashSet<BeadHash>
}