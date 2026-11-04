use crate::bead::Bead;
use crate::utils::BeadHash;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};

/// Maximum number of orphan beads parked while waiting for a missing parent.
///
/// Beads arriving over gossip are not proof-of-work checked, so parking one
/// costs an attacker nothing. This cap is what keeps a flood of beads with
/// fabricated parent hashes from growing the buffer without limit. Legitimate
/// out-of-order delivery resolves within a few bead intervals (~150ms each),
/// so 1024 leaves a wide margin for reordering and sync bursts while still
/// bounding the buffer.
pub const MAX_ORPHAN_BEADS: usize = 1024;

/// Beads that arrived before their parents, indexed so that the arrival of a
/// parent hash can find exactly the orphans waiting on it.
///
/// The pool keys beads by their own hash, so a bead re-sent any number of times
/// occupies one slot. Capacity is bounded; when full, the oldest parked bead is
/// evicted to make room for the newest.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OrphanPool {
    /// Parked beads, keyed by their own hash so duplicates collapse.
    beads: HashMap<BeadHash, Bead>,
    /// Missing parent hash -> hashes of the orphans blocked on it. An orphan is
    /// registered under exactly one missing parent at a time: the first one
    /// found absent. If that parent arrives while others are still missing, the
    /// orphan is re-parked under the next absent parent.
    waiting_on: HashMap<BeadHash, HashSet<BeadHash>>,
    /// Parked hashes in arrival order, used to pick an eviction victim.
    order: VecDeque<BeadHash>,
    /// Maximum number of beads held at once.
    capacity: usize,
}

impl Default for OrphanPool {
    fn default() -> Self {
        Self::new()
    }
}

impl OrphanPool {
    /// Creates an empty pool holding at most [`MAX_ORPHAN_BEADS`] beads.
    pub fn new() -> Self {
        Self::with_capacity(MAX_ORPHAN_BEADS)
    }

    /// Creates an empty pool holding at most `capacity` beads.
    ///
    /// A capacity of zero disables parking entirely: [`park`](Self::park) keeps
    /// nothing.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            beads: HashMap::new(),
            waiting_on: HashMap::new(),
            order: VecDeque::new(),
            capacity,
        }
    }

    /// Number of beads currently parked.
    pub fn len(&self) -> usize {
        self.beads.len()
    }

    /// Whether any beads are parked.
    pub fn is_empty(&self) -> bool {
        self.beads.is_empty()
    }

    /// Maximum number of beads this pool will hold.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Whether a bead with this hash is already parked.
    pub fn contains(&self, bead_hash: &BeadHash) -> bool {
        self.beads.contains_key(bead_hash)
    }

    /// Iterates over the parked beads in unspecified order.
    pub fn iter(&self) -> impl Iterator<Item = &Bead> {
        self.beads.values()
    }

    /// Drops every parked bead.
    pub fn clear(&mut self) {
        self.beads.clear();
        self.waiting_on.clear();
        self.order.clear();
    }

    /// Parks `bead` until `missing_parent` arrives.
    ///
    /// Re-parking a bead already held updates which parent it waits on and
    /// leaves its position in the eviction order untouched, so replaying a bead
    /// cannot push other orphans out. Returns `true` if the bead is parked
    /// afterwards, `false` if it was dropped because the pool is full and the
    /// bead is the newest (only possible with a zero capacity).
    pub fn park(&mut self, bead_hash: BeadHash, bead: Bead, missing_parent: BeadHash) -> bool {
        if self.beads.contains_key(&bead_hash) {
            // Already parked: it may now be blocked on a different parent.
            self.clear_waiting_edges(&bead_hash);
            self.waiting_on
                .entry(missing_parent)
                .or_default()
                .insert(bead_hash);
            return true;
        }

        if self.capacity == 0 {
            return false;
        }

        while self.beads.len() >= self.capacity {
            if !self.evict_oldest() {
                return false;
            }
        }

        self.beads.insert(bead_hash, bead);
        self.order.push_back(bead_hash);
        self.waiting_on
            .entry(missing_parent)
            .or_default()
            .insert(bead_hash);
        true
    }

    /// Removes and returns the orphans waiting on `parent_hash`.
    ///
    /// This is the seed for iterative promotion: when a bead is connected, only
    /// the orphans blocked on *its* hash can have become connectable, so there
    /// is no need to rescan the whole pool.
    pub fn take_waiting_on(&mut self, parent_hash: &BeadHash) -> Vec<Bead> {
        let Some(waiting) = self.waiting_on.remove(parent_hash) else {
            return Vec::new();
        };

        let mut released = Vec::with_capacity(waiting.len());
        for orphan_hash in waiting {
            if let Some(bead) = self.beads.remove(&orphan_hash) {
                self.order.retain(|hash| hash != &orphan_hash);
                released.push(bead);
            }
        }
        released
    }

    /// Drops the oldest parked bead. Returns `false` if the pool is empty.
    fn evict_oldest(&mut self) -> bool {
        while let Some(oldest) = self.order.pop_front() {
            if self.beads.remove(&oldest).is_some() {
                self.clear_waiting_edges(&oldest);
                return true;
            }
        }
        false
    }

    /// Removes `bead_hash` from every `waiting_on` bucket that mentions it.
    fn clear_waiting_edges(&mut self, bead_hash: &BeadHash) {
        self.waiting_on.retain(|_, waiting| {
            waiting.remove(bead_hash);
            !waiting.is_empty()
        });
    }
}
