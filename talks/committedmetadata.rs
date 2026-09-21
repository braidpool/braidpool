pub struct CommittedMetadata {
    pub transactions: Vec<Transaction>,    // 2-5 transactions added to committed mempool
    pub parents: Vec<BeadHash>,            // Parent beads
    pub payout_address: P2P_Address,       // Payout address for this miner
    pub start_time: Time,                  // When the miner started mining this bead
    pub comm_pubkey: PublicKey,            // Pubkey for ECIES encrypted miner communication
    pub miner_ip: AddrV2,                  // Miner IP address
}
