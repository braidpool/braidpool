// Custom Imports
use crate::utils::Hash;
use crate::utils::bitcoin::{Transaction, MerkleHash, BlockHeader};

struct BeadCommittedMetadata<'a> {
    lesser_target_difficulty: u32,
    parents: Vec<(&'a DagBead<'a>, u32)>
}

pub struct DagBead<'a> {
    block_header: BlockHeader,
    bead_hash: Hash,
    coinbase_transaction: Transaction,
    payout_update_transaction: Transaction,
    bead_committed_metadata: BeadCommittedMetadata<'a>
}

pub struct NetworkBead<'a> {
    block_header: BlockHeader,
    coinbase_transaction: Transaction,
    payout_update_transaction: Transaction,
    bead_committed_metadata: BeadCommittedMetadata<'a>
}