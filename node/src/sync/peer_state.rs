use crate::utils::BeadHash;
use libp2p::PeerId;

// All the states related to a sync peer including the
// hash queue, next-offset and tips originally stored
// till IBD is not completed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyncPeerState {
    /// The peer we are currently syncing from.
    pub peer: PeerId,
    /// Tips advertised by the peer (from the `GetTips` response). Used to prune
    /// the hash page so we stop once all of the peer's tips are covered.
    pub peer_tips: Vec<BeadHash>,
    /// The current page of bead hashes being downloaded (post-pruning).
    pub queue: Vec<BeadHash>,
    /// Number of hashes from `queue` already requested via `GetBeads`.
    pub offset: usize,
}

impl SyncPeerState {
    /// Start tracking a freshly selected sync target with empty cursors.
    pub fn new(peer: PeerId) -> Self {
        Self {
            peer,
            peer_tips: Vec::new(),
            queue: Vec::new(),
            offset: 0,
        }
    }
}
