use crate::bead::Bead;
use crate::braid::Braid;
use crate::config::PoolNetwork;
use crate::edca::cmempool_state::{EpochState, StateKey};
use crate::edca::validate_fees::{
    verify_fee_against_template, ChainAnchor, FeeVerdict, FeeVerdictSource, TemplateCache,
    TemplateEntry,
};
use crate::error::FeeProofError;
use crate::utils::{compute_block_hash, BeadHash};
use bitcoin::{BlockHash, Txid};
use std::collections::HashMap;
use std::sync::Arc;

/// A [`BeadValidator`] shared by the template consumer and every path that adds
/// beads to the braid. Take the braid lock first when both are needed.
pub type SharedBeadValidator = Arc<tokio::sync::Mutex<BeadValidator>>;

/// Returns the fees of a template's non-coinbase transactions.
///
/// Bitcoin Core reports either one fee per transaction with the coinbase in
/// slot zero, or one fee per non-coinbase transaction. `None` when `fees`
/// matches neither shape for a template of `transaction_count` transactions,
/// coinbase included.
pub fn non_coinbase_fees(fees: &[u64], transaction_count: usize) -> Option<&[u64]> {
    let non_coinbase_count = transaction_count.checked_sub(1)?;
    if fees.len() == transaction_count {
        fees.get(1..)
    } else if fees.len() == non_coinbase_count {
        Some(fees)
    } else {
        None
    }
}

/// Validates the fee claim of every bead as it enters the braid.
///
/// A bead's committed-mempool state is derived from its ancestors and looked
/// up among the templates this node issued. On a hit the bead's coinbase, fee
/// total and committed transactions are checked against that template; the
/// verdict is stored once and read back when the bead is scored.
#[derive(Debug, Clone)]
pub struct BeadValidator {
    /// Network this node runs on, deciding bead hashing and the subsidy.
    network: PoolNetwork,
    /// Ancestor-derived states for the Bitcoin block currently mined on.
    epoch: Option<EpochState>,
    /// Templates this node issued on the current block.
    templates: TemplateCache,
    /// Verdict of every bead validated so far.
    verdicts: HashMap<BeadHash, FeeVerdict>,
}

impl BeadValidator {
    /// Creates a validator with no templates and no verdicts.
    pub fn new(network: PoolNetwork) -> Self {
        Self {
            network,
            epoch: None,
            templates: TemplateCache::new(),
            verdicts: HashMap::new(),
        }
    }

    /// Records a template this node issued.
    ///
    /// A template on a new Bitcoin block starts a new epoch: the derived
    /// states and the templates of the previous block are dropped. Only this
    /// node's own templates move the epoch, so a peer cannot reset it.
    pub fn insert_template(&mut self, template: TemplateEntry) {
        let anchor = template.anchor.prev_blockhash;
        if self.epoch.as_ref().map(EpochState::anchor) != Some(anchor) {
            self.epoch = Some(EpochState::new(anchor));
            self.templates.retain_block(anchor);
        }
        self.templates.insert(template);
    }

    /// Prices and records a template from the parts Bitcoin Core returned.
    ///
    /// `committed_txids` are the template's transactions without the coinbase,
    /// and `fees_sats` carries one fee for each of them.
    pub fn insert_template_parts(
        &mut self,
        prev_blockhash: BlockHash,
        height: u64,
        committed_txids: &[Txid],
        coinbase_merkle_path: &[Vec<u8>],
        fees_sats: &[u64],
    ) -> Result<StateKey, FeeProofError> {
        if committed_txids.len() != fees_sats.len() {
            return Err(FeeProofError::FeeCountMismatch {
                transactions: committed_txids.len(),
                fees: fees_sats.len(),
            });
        }
        let state_key = StateKey::from_txids(committed_txids);
        let template = TemplateEntry::from_branch_bytes(
            ChainAnchor::new(prev_blockhash, height, self.network),
            state_key,
            coinbase_merkle_path,
            fees_sats,
        )?;
        self.insert_template(template);
        Ok(state_key)
    }

    /// Validates a bead that was just added to `braid` and stores the verdict.
    ///
    /// The bead stays in the braid whatever the verdict; only a `Verified`
    /// bead earns fee credit.
    pub fn on_bead_added(&mut self, braid: &Braid, bead: &Bead) -> FeeVerdict {
        let bead_hash = compute_block_hash(&bead.block_header, self.network);
        let verdict = self.validate(braid, bead, bead_hash);
        self.verdicts.insert(bead_hash, verdict);
        verdict
    }

    /// Validates a bead that was just added to `braid`, then each orphan its
    /// arrival promoted, in the order they were promoted.
    pub fn on_beads_added(&mut self, braid: &Braid, bead: &Bead, promoted_orphans: &[Bead]) {
        self.on_bead_added(braid, bead);
        for orphan in promoted_orphans {
            self.on_bead_added(braid, orphan);
        }
    }

    /// Restores a verdict persisted by an earlier run of this node.
    pub fn restore_verified(&mut self, bead_hash: BeadHash, fee_sats: u64) {
        self.verdicts
            .insert(bead_hash, FeeVerdict::Verified { fee_sats });
    }

    /// Returns the stored verdict for the bead with `bead_hash`, if it was
    /// validated.
    pub fn verdict_of(&self, bead_hash: &BeadHash) -> Option<FeeVerdict> {
        self.verdicts.get(bead_hash).copied()
    }

    /// Returns the fee this node verified for `bead`, if any.
    pub fn verified_fee_sats(&self, bead: &Bead) -> Option<u64> {
        match self.verdict(bead) {
            FeeVerdict::Verified { fee_sats } => Some(fee_sats),
            FeeVerdict::Deviated | FeeVerdict::Unknown => None,
        }
    }

    /// Returns how many templates are retained for the current block.
    pub fn template_count(&self) -> usize {
        self.templates.len()
    }

    /// Derives the bead's state, finds the template built from it and checks
    /// the bead against that template.
    fn validate(&mut self, braid: &Braid, bead: &Bead, bead_hash: BeadHash) -> FeeVerdict {
        let Some(epoch) = self.epoch.as_mut() else {
            return FeeVerdict::Unknown;
        };
        let Some(&bead_index) = braid.bead_index_mapping.get(&bead_hash) else {
            return FeeVerdict::Unknown;
        };
        let Some(state_key) = epoch.state_key(braid, bead_index) else {
            return FeeVerdict::Unknown;
        };
        let Some(template) = self
            .templates
            .get(bead.block_header.prev_blockhash, state_key)
        else {
            return FeeVerdict::Unknown;
        };

        match check_against_template(bead, state_key, template) {
            Ok(fee_sats) => FeeVerdict::Verified { fee_sats },
            Err(error) => {
                tracing::warn!(
                    hash = %bead_hash,
                    error = ?error,
                    "Bead deviates from the template its state selects"
                );
                FeeVerdict::Deviated
            }
        }
    }
}

/// Checks a bead against the template built from its derived state and returns
/// the verified fee total.
fn check_against_template(
    bead: &Bead,
    state_key: StateKey,
    template: &TemplateEntry,
) -> Result<u64, FeeProofError> {
    let metadata = &bead.committed_metadata;

    // The transactions the bead says it mined must be the derived state.
    if metadata.committed_txs.0.len() != template.tx_count
        || StateKey::from_txids(&metadata.committed_txs.0) != state_key
    {
        return Err(FeeProofError::CommittedTransactionsMismatch);
    }

    let coinbase = &metadata.coinbase_transaction;
    if !coinbase.is_coinbase() {
        return Err(FeeProofError::NotCoinbase);
    }

    // Anchor, merkle fold and fee total.
    let commitment = verify_fee_against_template(bead, coinbase.compute_txid(), template)?;

    // The coinbase may not pay out more than subsidy plus the template's fees.
    let coinbase_output_sats = coinbase
        .output
        .iter()
        .try_fold(0u64, |total, output| {
            total.checked_add(output.value.to_sat())
        })
        .ok_or(FeeProofError::CoinbaseValueOverflow)?;
    if coinbase_output_sats > commitment.coinbase_value_sats {
        return Err(FeeProofError::CoinbaseOverpays {
            coinbase_output_sats,
            allowed_sats: commitment.coinbase_value_sats,
        });
    }

    Ok(commitment.fee_total_sats)
}

impl FeeVerdictSource for BeadValidator {
    fn verdict(&self, bead: &Bead) -> FeeVerdict {
        self.verdicts
            .get(&compute_block_hash(&bead.block_header, self.network))
            .copied()
            .unwrap_or(FeeVerdict::Unknown)
    }
}

