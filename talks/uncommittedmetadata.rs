pub struct UnCommittedMetadata {
    pub extranonce: i32,                   // Extranonce used to find this solution
    pub broadcast_timestamp: Time,         // When the miner broadcast this solution
    pub parent_bead_timestamps: Vec<Time>, // Observation when this node saw its parents
    pub signature: Signature               // Signature on the above uncommitted metadata
}
