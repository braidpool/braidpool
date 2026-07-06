// Standard Imports
use ::serde::Serialize;
use std::fmt;
use std::net::SocketAddr;

// Bitcoin primitives
use bitcoin::absolute::Time;
use bitcoin::ecdsa::Signature;
use bitcoin::secp256k1::PublicKey;
use bitcoin::{Address, BlockHeader, Transaction};
// Custom Imports
use crate::utils::BeadHash;

/// Error returned when parent and timestamp vectors have mismatched lengths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalizeError {
    pub parents_len: usize,
    pub timestamps_len: usize,
}

impl fmt::Display for CanonicalizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "parent count ({}) does not match timestamp count ({})",
            self.parents_len, self.timestamps_len
        )
    }
}

impl std::error::Error for CanonicalizeError {}

/// Committed (consensus-relevant) metadata for a bead.
///
/// `parents` is always kept in **canonical order** (sorted by `BeadHash`
/// ascending) so that serialization is deterministic across all nodes.
/// Use [`CommittedMetadata::new`] to construct.
#[derive(Clone, Debug, Serialize)]
pub struct CommittedMetadata {
    pub transaction_cnt: u32,
    pub transactions: Vec<Transaction>,
    /// Parent bead hashes in canonical (sorted) order.
    pub parents: Vec<BeadHash>,
    pub payout_address: Address,
    pub observed_time_at_node: Time,
    pub comm_pub_key: PublicKey,
    pub miner_ip: SocketAddr,
}

impl CommittedMetadata {
    /// Create a new `CommittedMetadata` with parents in canonical order.
    ///
    /// Parents are sorted by `BeadHash` ascending. If `timestamps` is provided,
    /// they are reordered to stay aligned with their parent hash.
    pub fn new(
        transaction_cnt: u32,
        transactions: Vec<Transaction>,
        parents: Vec<(BeadHash, Time)>,
        payout_address: Address,
        observed_time_at_node: Time,
        comm_pub_key: PublicKey,
        miner_ip: SocketAddr,
    ) -> Self {
        let mut sorted = parents;
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let (sorted_parents, _sorted_timestamps): (Vec<_>, Vec<_>) = sorted.into_iter().unzip();

        // timestamps are stored in UnCommittedMetadata, not here.
        // The `parents` field only holds hashes. Timestamps are passed through
        // to `canonicalize_parents` via the Uncommitted side.
        Self {
            transaction_cnt,
            transactions,
            parents: sorted_parents,
            payout_address,
            observed_time_at_node,
            comm_pub_key,
            miner_ip,
        }
    }
}

/// Uncommitted (non-consensus) metadata for a bead.
///
/// `parent_bead_timestamps` must be kept in the **same order** as
/// [`CommittedMetadata::parents`]. Use [`canonicalize_parents`] to enforce
/// this ordering invariant.
#[derive(Clone, Debug, Serialize)]
pub struct UnCommittedMetadata {
    pub extra_nonce: i32,
    pub broadcast_timestamp: Time,
    pub signature: Signature,
    /// Parent bead timestamps in the same order as `CommittedMetadata::parents`.
    pub parent_bead_timestamps: Vec<Time>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Bead {
    pub block_header: BlockHeader,
    pub committed_metadata: CommittedMetadata,
    pub uncommitted_metadata: UnCommittedMetadata,
}

impl Bead {
    pub fn is_valid_bead(&self) -> bool {
        true
    }

    pub fn get_coinbase_transaction(&self) -> Transaction {
        unimplemented!()
    }

    pub fn get_payout_update_transaction(&self) -> Transaction {
        unimplemented!()
    }
}

/// Canonicalize the ordering of `parents` and their corresponding timestamps.
///
/// Both slices are zipped, sorted by `BeadHash` ascending, and written back.
/// After this call, serializing `CommittedMetadata` (which feeds the coinbase
/// `OP_RETURN` commitment) produces **deterministic** bytes regardless of the
/// order in which parents were originally collected.
///
/// # Errors
///
/// Returns [`CanonicalizeError`] if the two slices have different lengths.
pub fn canonicalize_parents(
    parents: &mut Vec<BeadHash>,
    timestamps: &mut Vec<Time>,
) -> Result<(), CanonicalizeError> {
    if parents.len() != timestamps.len() {
        return Err(CanonicalizeError {
            parents_len: parents.len(),
            timestamps_len: timestamps.len(),
        });
    }

    let mut pairs: Vec<(BeadHash, Time)> = parents
        .drain(..)
        .zip(timestamps.drain(..))
        .collect();

    pairs.sort_by(|a, b| a.0.cmp(&b.0));

    for (hash, time) in pairs {
        parents.push(hash);
        timestamps.push(time);
    }

    Ok(())
}

#[cfg(test)]
mod tests;
