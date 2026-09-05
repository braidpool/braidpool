pub struct Bead {
    pub block_header: BlockHeader,         // Standard Bitcoin block header
    pub committed: CommittedMetadata,      // Committed to in coinbase OP_RETURN
    pub uncommitted: UnCommittedMetadata,  // Not committed to in coinbase
}
