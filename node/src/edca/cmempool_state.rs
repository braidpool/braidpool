use crate::braid::Braid;
use bitcoin::hashes::{sha256d, Hash, HashEngine};
use bitcoin::{BlockHash, Txid};
use std::collections::HashMap;

/// Identifies a committed-mempool state by the transactions it holds.
///
/// The digest covers the txids sorted by their raw bytes, so it depends only
/// on which transactions are present and is the same on every node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateKey([u8; 32]);

impl StateKey {
    /// Derives the key of the state holding exactly `txids`.
    pub fn from_txids<'a>(txids: impl IntoIterator<Item = &'a Txid>) -> Self {
        let mut sorted: Vec<[u8; 32]> =
            txids.into_iter().map(|txid| txid.to_byte_array()).collect();
        sorted.sort_unstable();
        sorted.dedup();
        let mut engine = sha256d::Hash::engine();
        for txid in &sorted {
            engine.input(txid);
        }
        StateKey(sha256d::Hash::from_engine(engine).to_byte_array())
    }

    /// Returns the raw digest.
    pub fn to_byte_array(self) -> [u8; 32] {
        self.0
    }
}

/// The committed-mempool state one bead was mined on.
#[derive(Debug, Clone, PartialEq, Eq)]
struct BeadState {
    /// Bit `n` is set when `EpochState::txids[n]` is in the state.
    members: Vec<u64>,
    /// Key of the state, computed once when the bead is recorded.
    key: StateKey,
}

/// Committed-mempool states of every bead mined on one Bitcoin block.
///
/// A bead's state is the union of what its ancestors proposed in
/// `to_be_added`; its own proposals count only for its descendants. Each state
/// is built from the states of the bead's parents, so no ancestor walk is
/// needed, and is stored as a bitset over the transactions seen this epoch.
#[derive(Debug, Clone)]
pub struct EpochState {
    /// The Bitcoin block every bead of this epoch builds on.
    anchor: BlockHash,
    /// Every transaction proposed this epoch, in order of first appearance.
    txids: Vec<Txid>,
    /// Position of each transaction in `txids`.
    index: HashMap<Txid, u32>,
    /// State of each recorded bead, keyed by its index in the braid.
    per_bead: HashMap<usize, BeadState>,
}

impl EpochState {
    /// Starts an empty epoch on `anchor`.
    pub fn new(anchor: BlockHash) -> Self {
        Self {
            anchor,
            txids: Vec::new(),
            index: HashMap::new(),
            per_bead: HashMap::new(),
        }
    }

    /// Returns the Bitcoin block this epoch builds on.
    pub fn anchor(&self) -> BlockHash {
        self.anchor
    }

    /// Returns how many distinct transactions were proposed this epoch.
    pub fn transaction_count(&self) -> usize {
        self.txids.len()
    }

    /// Returns how many beads have a recorded state.
    pub fn bead_count(&self) -> usize {
        self.per_bead.len()
    }

    /// Returns the key of the state the bead at `bead_index` was mined on,
    /// deriving and recording it first if needed.
    ///
    /// `None` when the bead is not in `braid`, builds on another Bitcoin
    /// block, or names a parent the braid does not hold.
    pub fn state_key(&mut self, braid: &Braid, bead_index: usize) -> Option<StateKey> {
        let bead = braid.beads.get(bead_index)?;
        if bead.block_header.prev_blockhash != self.anchor {
            return None;
        }

        // Parents are recorded before their children. A parent that arrived
        // before this epoch began is derived here on demand, with an explicit
        // stack so a long chain cannot overflow the call stack.
        let mut pending = vec![bead_index];
        while let Some(&current) = pending.last() {
            if self.per_bead.contains_key(&current) {
                pending.pop();
                continue;
            }
            let parents = self.epoch_parents(braid, current)?;
            let unrecorded: Vec<usize> = parents
                .iter()
                .copied()
                .filter(|parent| !self.per_bead.contains_key(parent))
                .collect();
            if unrecorded.is_empty() {
                let state = self.derive(braid, &parents)?;
                self.per_bead.insert(current, state);
                pending.pop();
            } else {
                pending.extend(unrecorded);
            }
        }

        self.per_bead.get(&bead_index).map(|state| state.key)
    }

    /// Returns the transactions in the recorded state of the bead at
    /// `bead_index`, in order of first appearance this epoch.
    pub fn members(&self, bead_index: usize) -> Option<Vec<Txid>> {
        let state = self.per_bead.get(&bead_index)?;
        Some(self.member_txids(&state.members).copied().collect())
    }

    /// Returns the braid indices of the parents of `bead_index` that build on
    /// this epoch's Bitcoin block. Parents on another block carry no state
    /// into this epoch.
    fn epoch_parents(&self, braid: &Braid, bead_index: usize) -> Option<Vec<usize>> {
        let bead = braid.beads.get(bead_index)?;
        let mut parents = Vec::with_capacity(bead.committed_metadata.parents.len());
        for parent_hash in &bead.committed_metadata.parents {
            let parent_index = *braid.bead_index_mapping.get(parent_hash)?;
            // A parent is always inserted before its child.
            if parent_index >= bead_index {
                return None;
            }
            let parent = braid.beads.get(parent_index)?;
            if parent.block_header.prev_blockhash == self.anchor {
                parents.push(parent_index);
            }
        }
        Some(parents)
    }

    /// Builds a bead's state from its already recorded `parents`: each parent
    /// contributes its own state and the transactions it proposed.
    fn derive(&mut self, braid: &Braid, parents: &[usize]) -> Option<BeadState> {
        let mut members: Vec<u64> = Vec::new();
        for parent_index in parents {
            let parent_state = self.per_bead.get(parent_index)?;
            if members.len() < parent_state.members.len() {
                members.resize(parent_state.members.len(), 0);
            }
            for (word, parent_word) in members.iter_mut().zip(&parent_state.members) {
                *word |= parent_word;
            }
        }
        for parent_index in parents {
            let parent = braid.beads.get(*parent_index)?;
            for txid in &parent.committed_metadata.to_be_added.0 {
                let position = self.intern(*txid)? as usize;
                let word = position / 64;
                if members.len() <= word {
                    members.resize(word + 1, 0);
                }
                members[word] |= 1u64 << (position % 64);
            }
        }
        let key = StateKey::from_txids(self.member_txids(&members));
        Some(BeadState { members, key })
    }

    /// Returns the position of `txid` in this epoch's transaction list,
    /// appending it if it is new.
    fn intern(&mut self, txid: Txid) -> Option<u32> {
        if let Some(position) = self.index.get(&txid) {
            return Some(*position);
        }
        let position = u32::try_from(self.txids.len()).ok()?;
        self.txids.push(txid);
        self.index.insert(txid, position);
        Some(position)
    }

    /// Iterates the transactions whose bits are set in `members`.
    fn member_txids<'a>(&'a self, members: &'a [u64]) -> impl Iterator<Item = &'a Txid> {
        self.txids
            .iter()
            .enumerate()
            .filter(move |(position, _)| {
                members
                    .get(position / 64)
                    .is_some_and(|word| word & (1u64 << (position % 64)) != 0)
            })
            .map(|(_, txid)| txid)
    }
}
