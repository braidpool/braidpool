/// A Bitcoin block template, as sent from the braidpool node to the SV2 pool.
///
/// Both crates (`braidpool-node` and `sv2-apps/pool`) depend on this type via
/// `braidpool-common`. Fields must match exactly — changing one side requires
/// changing both.
#[derive(Debug, Clone)]
pub struct BraidpoolTemplate {
    /// Serialized coinbase transaction (consensus encoding).
    pub coinbase_tx: Vec<u8>,
    /// Merkle path from coinbase to block root, each entry is a 32-byte hash.
    pub merkle_path: Vec<[u8; 32]>,
    /// `prevhash` field from the block header (little-endian).
    pub prev_hash: [u8; 32],
    /// Compact target (`nBits`) from the block header.
    pub nbits: u32,
    /// `nTime` from the block header at the moment the template was created.
    pub header_timestamp: u32,
    /// Block version field (may include BIP-320 rolled bits).
    pub version: i32,
    /// Block height. Comes from the IPC `TipChanged` notification, not from
    /// `BlockTemplate.height` (which is `Height::ZERO` in some code paths).
    pub height: u32,
    /// Opaque ID assigned by `ipc_template_consumer` for share-to-template
    /// matching. Corresponds to `TemplateId::Braidpool(u64)`.
    pub template_id: u64,
}
