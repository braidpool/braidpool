use crate::bead::{Bead, BeadHashes, BeadRequest};
use crate::utils::BeadHash;
use libp2p::PeerId;
use std::collections::{HashMap, HashSet};
use std::time::Duration;

pub mod ingest_beads;
pub mod peer_state;
pub mod retry;

pub use peer_state::SyncPeerState;
pub use retry::RetryPolicy;

/// Maximum number of beads requested per `GetBeads` round-trip.
pub const IBD_BATCH_SIZE: usize = 500;
/// Maximum number of bead hashes a single `GetBeadsAfter` page may contain.
/// A larger response is treated as a protocol violation.
pub const IBD_HASH_PAGE_MAX: usize = 5_000;

/// Where IBD currently is. Single-peer: at most one active sync target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyncState {
    /// Not syncing. Either pre-trigger or between retries.
    Idle,
    /// Sent `GetTips`, awaiting the peer's tips.
    AwaitingTips,
    /// Sent `GetBeadsAfter`, awaiting a page of bead hashes.
    FetchingHashes,
    /// Downloading the beads for the current hash page in batches.
    FetchingBeads,
    /// IBD finished.
    Complete,
}

/// Inputs to the engine for triggering SyncActions on the basis of event received in the
/// main event loop .
#[derive(Debug, Clone)]
pub enum SyncEvent {
    /// Begin (or retry) IBD against a peer the adapter has already selected.
    /// upon retry the previous state is preserved still .
    Start { peer: PeerId },
    /// The adapter could not find any peer to sync from.
    NoPeerAvailable,
    /// Peer answered `GetTips`. `already_synced` is true when every one of the
    /// peer's tips is already present in our braid (computed by the adapter).
    TipsReceived {
        peer: PeerId,
        peer_tips: Vec<BeadHash>,
        already_synced: bool,
    },
    /// Peer answered `GetBeadsAfter` with a page of bead hashes.
    HashPageReceived { peer: PeerId, hashes: Vec<BeadHash> },
    /// Peer answered `GetBeads` with the actual beads. The engine validates them
    /// against the requested page (anti-spam) and hands the valid ones to the
    /// adapter via [`SyncAction::ApplyBeads`].
    ///
    /// Note: the engine does **not** take the braid tips here. The next hash page
    /// must be requested relative to the tips *after* this batch is applied, so
    /// that request is expressed as [`SyncAction::RequestHashPage`] and the
    /// adapter reads the (post-apply) tips when it executes it.
    BeadsReceived { peer: PeerId, beads: Vec<Bead> },
    /// The active outbound request failed.
    RequestFailed { peer: PeerId },
    /// The active outbound request timed out.
    Timeout { peer: PeerId },
    /// The active sync peer disconnected.
    PeerDisconnected { peer: PeerId },
}

/// Outputs from the engine, executed by the ingest handler.
#[derive(Debug, Clone, PartialEq)]
pub enum SyncAction {
    /// Send a fully-formed bead-sync request to `peer`. The adapter records the returned request id as
    /// the in-flight request for timeout/failure correlation.
    SendRequest { peer: PeerId, request: BeadRequest },
    /// Ask `peer` for the next page of bead hashes *after our current tips*.
    ///
    /// This is deliberately a separate action rather than a `SendRequest`
    /// carrying tips: when it follows an [`SyncAction::ApplyBeads`] in the same
    /// action list, the adapter must read the braid's tips *after* applying that
    /// batch — otherwise the next page would be requested after stale tips and
    /// re-download the page just applied. The adapter forms
    /// `GetBeadsAfter(current_tips)` at execution time.
    RequestHashPage { peer: PeerId },
    /// Ingest these beads — the adapter extends the braid
    ///  and persists them  Always executed before any [`SyncAction::RequestHashPage`] that follows it.
    ApplyBeads { beads: Vec<Bead> },
    /// Drop `peer` (invalid bead or oversized hash page).
    DisconnectPeer { peer: PeerId },
    /// Wait `after`, then the adapter selects a peer and re-issues [`SyncEvent::Start`].
    ScheduleRetry { after: Duration },
    /// IBD finished; the adapter flips the `ibd_complete` flag.
    MarkComplete,
}

/// The IBD protocol state machine.
#[derive(Debug)]
pub struct SyncEngine {
    state: SyncState,
    /// The single active sync target, if any.
    active: Option<SyncPeerState>,
    /// Consecutive IBD failures per peer. A peer reaching the retry ceiling is
    /// surfaced via [`SyncEngine::exhausted_peers`] so the adapter excludes it
    /// from sync-peer selection  according to max_retries.
    retries: HashMap<PeerId, u64>,
    retry: RetryPolicy,
}

impl SyncEngine {
    /// Create an idle engine with the given retry policy.
    pub fn new(retry: RetryPolicy) -> Self {
        Self {
            state: SyncState::Idle,
            active: None,
            retries: HashMap::new(),
            retry,
        }
    }

    /// Current protocol state.
    pub fn state(&self) -> &SyncState {
        &self.state
    }

    /// The peer currently being synced from, if any.
    pub fn active_peer(&self) -> Option<PeerId> {
        self.active.as_ref().map(|p| p.peer)
    }

    /// Whether `peer` has reached the retry ceiling and should be excluded from
    /// sync-peer selection.
    pub fn is_exhausted(&self, peer: &PeerId) -> bool {
        self.retries.get(peer).copied().unwrap_or(0) >= self.retry.max_retries()
    }

    /// All peers currently at or over the retry ceiling — the adapter's
    /// exclusion set when (re-)selecting a sync peer.
    pub fn exhausted_peers(&self) -> Vec<PeerId> {
        let max = self.retry.max_retries();
        self.retries
            .iter()
            .filter(|(_, &count)| count >= max)
            .map(|(peer, _)| *peer)
            .collect()
    }

    /// Drive the state machine with one event, returning the actions to execute.
    pub fn on_event(&mut self, event: SyncEvent) -> Vec<SyncAction> {
        match event {
            SyncEvent::Start { peer } => self.on_start(peer),
            SyncEvent::NoPeerAvailable => self.on_no_peer(),
            SyncEvent::TipsReceived {
                peer,
                peer_tips,
                already_synced,
            } => self.on_tips(peer, peer_tips, already_synced),
            SyncEvent::HashPageReceived { peer, hashes } => self.on_hash_page(peer, hashes),
            SyncEvent::BeadsReceived { peer, beads } => self.on_beads(peer, beads),
            SyncEvent::RequestFailed { peer }
            | SyncEvent::Timeout { peer }
            | SyncEvent::PeerDisconnected { peer } => self.on_failure(peer),
        }
    }
    // This will reset the states hence should be called only once during an IBD if
    // no request gets timed out.
    fn on_start(&mut self, peer: PeerId) -> Vec<SyncAction> {
        self.active = Some(SyncPeerState::new(peer));
        self.state = SyncState::AwaitingTips;
        vec![SyncAction::SendRequest {
            peer,
            request: BeadRequest::GetTips,
        }]
    }

    fn on_no_peer(&mut self) -> Vec<SyncAction> {
        self.active = None;
        self.state = SyncState::Idle;
        vec![SyncAction::ScheduleRetry {
            after: self.retry.delay(0),
        }]
    }

    fn on_tips(
        &mut self,
        peer: PeerId,
        peer_tips: Vec<BeadHash>,
        already_synced: bool,
    ) -> Vec<SyncAction> {
        if !self.is_active(peer, SyncState::AwaitingTips) {
            return Vec::new();
        }
        if already_synced {
            return self.complete();
        }
        if let Some(active) = self.active.as_mut() {
            active.peer_tips = peer_tips;
        }
        self.state = SyncState::FetchingHashes;
        vec![SyncAction::RequestHashPage { peer }]
    }

    fn on_hash_page(&mut self, peer: PeerId, hashes: Vec<BeadHash>) -> Vec<SyncAction> {
        if !self.is_active(peer, SyncState::FetchingHashes) {
            return Vec::new();
        }
        // A peer that answers with more hashes than a page may hold is misbehaving.
        if hashes.len() > IBD_HASH_PAGE_MAX {
            return self.drop_peer(peer);
        }

        let pruned = match self.active.as_ref() {
            Some(active) => prune_to_tips(hashes, &active.peer_tips),
            None => return Vec::new(),
        };

        // Empty page -> nothing left to download; we are synced.
        if pruned.is_empty() {
            return self.complete();
        }

        let batch_end = pruned.len().min(IBD_BATCH_SIZE);
        let batch: Vec<BeadHash> = pruned[..batch_end].to_vec();
        if let Some(active) = self.active.as_mut() {
            active.queue = pruned;
            active.offset = batch_end;
        }
        self.state = SyncState::FetchingBeads;
        vec![SyncAction::SendRequest {
            peer,
            request: BeadRequest::GetBeads(BeadHashes(batch)),
        }]
    }

    fn on_beads(&mut self, peer: PeerId, beads: Vec<Bead>) -> Vec<SyncAction> {
        if !self.is_active(peer, SyncState::FetchingBeads) {
            return Vec::new();
        }

        let expected: HashSet<&BeadHash> = match self.active.as_ref() {
            Some(active) => active.queue.iter().collect(),
            None => return Vec::new(),
        };
        if beads
            .iter()
            .any(|bead| !expected.contains(&bead.block_header.block_hash()))
        {
            return self.drop_peer(peer);
        }

        // Hand the validated beads to the adapter to extend + persist .
        let mut actions = vec![SyncAction::ApplyBeads { beads }];

        let (offset, queue_len) = match self.active.as_ref() {
            Some(active) => (active.offset, active.queue.len()),
            None => return actions,
        };

        if offset < queue_len {
            // More batches remain in the current page.
            let batch_end = (offset + IBD_BATCH_SIZE).min(queue_len);
            let batch: Vec<BeadHash> = match self.active.as_ref() {
                Some(active) => active.queue[offset..batch_end].to_vec(),
                None => return actions,
            };
            if let Some(active) = self.active.as_mut() {
                active.offset = batch_end;
            }
            actions.push(SyncAction::SendRequest {
                peer,
                request: BeadRequest::GetBeads(BeadHashes(batch)),
            });
        } else if queue_len >= IBD_HASH_PAGE_MAX {
            // Page fetched completely but IBD requires more beads to be fetched
            // from the sync peer, thus requesting the new peer after extending these fetched beads .
            if let Some(active) = self.active.as_mut() {
                active.queue.clear();
                active.offset = 0;
            }
            self.state = SyncState::FetchingHashes;
            actions.push(SyncAction::RequestHashPage { peer });
        } else {
            //Short page -> IBD complete.
            actions.extend(self.complete());
        }
        actions
    }

    fn on_failure(&mut self, peer: PeerId) -> Vec<SyncAction> {
        // Ignore failures for non-active peers (stale / non-IBD requests).
        if self.active_peer() != Some(peer) {
            return Vec::new();
        }
        let count = {
            let entry = self.retries.entry(peer).or_insert(0);
            *entry += 1;
            *entry
        };
        self.active = None;
        self.state = SyncState::Idle;
        // Backoff grows with this peer's consecutive failures; the first retry
        // uses the base delay.
        vec![SyncAction::ScheduleRetry {
            after: self.retry.delay(count - 1),
        }]
    }

    /// Transition to `Complete`, clearing per-peer state and the retry counters
    /// so a future IBD starts fresh.
    fn complete(&mut self) -> Vec<SyncAction> {
        self.active = None;
        self.retries.clear();
        self.state = SyncState::Complete;
        vec![SyncAction::MarkComplete]
    }

    /// Drop the misbehaving sync peer and schedule a retry against another.
    ///
    /// This does not count toward the dropped peer's retry tally: the peer is
    /// being disconnected (not retried), so the adapter will simply select a
    /// different sync target.
    fn drop_peer(&mut self, peer: PeerId) -> Vec<SyncAction> {
        self.active = None;
        self.state = SyncState::Idle;
        vec![
            SyncAction::DisconnectPeer { peer },
            SyncAction::ScheduleRetry {
                after: self.retry.delay(0),
            },
        ]
    }

    /// True iff `peer` is the active sync target and the engine is in `expected`.
    fn is_active(&self, peer: PeerId, expected: SyncState) -> bool {
        self.state == expected && self.active_peer() == Some(peer)
    }
}

/// Prune a page of hashes down to the prefix that covers all of the peer's tips
fn prune_to_tips(hashes: Vec<BeadHash>, peer_tips: &[BeadHash]) -> Vec<BeadHash> {
    if peer_tips.is_empty() {
        return hashes;
    }
    let tips_set: HashSet<&BeadHash> = peer_tips.iter().collect();
    let mut found: HashSet<BeadHash> = HashSet::new();
    let mut pruned = Vec::new();
    for hash in hashes {
        if tips_set.contains(&hash) {
            found.insert(hash);
        }
        pruned.push(hash);
        if found.len() == tips_set.len() {
            break;
        }
    }
    pruned
}
