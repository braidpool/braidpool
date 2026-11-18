use crate::bead::Bead;
use crate::edca::decay::DecayTable;
use crate::edca::fixed::{mul_frac, ratio_q, target_to_biguint, ONE};
use crate::edca::validate_fees::{FeeVerdict, FeeVerdictSource};
use crate::error::EdcaError;

/// Supplies the per-bead transaction fee total `F_i` that will be
/// added to base_i .
pub trait AmplifierSource {
    /// Returns `F_i`, the total transaction fees in this bead's committed block
    /// template, in satoshis.
    fn fee_sats(&self, bead: &Bead) -> Result<u64, EdcaError>;
}

/// Interim [`AmplifierSource`] that reports `F_i = 0`, so `A_i = B_base`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SubsidyOnlyAmplifier;

impl AmplifierSource for SubsidyOnlyAmplifier {
    fn fee_sats(&self, _bead: &Bead) -> Result<u64, EdcaError> {
        Ok(0)
    }
}

/// [`AmplifierSource`] that reads `F_i` from the bead's committed metadata.
///
/// The value is whatever the miner committed, checked against nothing, so a
/// bead can claim any fee total and be scored on it. Prefer
/// [`VerdictAmplifier`], which pays only fees the node computed from its own
/// template; this one remains for tests and for scoring a DAG whose templates
/// the node cannot rebuild.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CommittedFeeAmplifier;

impl AmplifierSource for CommittedFeeAmplifier {
    fn fee_sats(&self, bead: &Bead) -> Result<u64, EdcaError> {
        Ok(bead
            .committed_metadata
            .fee_total_sats
            .min(bitcoin::Amount::MAX_MONEY.to_sat()))
    }
}

/// [`AmplifierSource`] that pays only fees this node verified itself.
///
/// The fee comes from a [`TemplateEntry`](crate::edca::TemplateEntry) this node
/// issued and priced itself, so a miner cannot inflate `A_i` by claiming fees
/// they never carried. A bead that mined a different template, or one this node
/// no longer holds, scores `F_i = 0` rather than failing the state - the same
/// treatment a zero-target bead gets.
pub struct VerdictAmplifier<'a> {
    verdicts: &'a dyn FeeVerdictSource,
}

impl<'a> VerdictAmplifier<'a> {
    /// Scores beads against `verdicts`.
    pub fn new(verdicts: &'a dyn FeeVerdictSource) -> Self {
        Self { verdicts }
    }
}

impl AmplifierSource for VerdictAmplifier<'_> {
    fn fee_sats(&self, bead: &Bead) -> Result<u64, EdcaError> {
        Ok(match self.verdicts.verdict(bead) {
            FeeVerdict::Verified { fee_sats } => fee_sats,
            FeeVerdict::Deviated | FeeVerdict::Unknown => 0,
        })
    }
}

/// Computes the fee amplifier `A_i = B_base + F_i` of .
pub fn fee_amplifier(base_subsidy_sats: u64, fee_sats: u64) -> Result<u64, EdcaError> {
    base_subsidy_sats
        .checked_add(fee_sats)
        .ok_or(EdcaError::AmplifierOverflow)
}

/// Computes the probability factor `D_bp / D_network` .
///
/// This is the strict mathematical probability that any single bead is also a
/// valid Bitcoin block. Difficulty is inversely proportional to target
/// (`D = T_max / T`), so
///
/// ```text
/// D_bp / D_network = (T_max / T_bp) / (T_max / T_net) = T_net / T_bp
/// ```
///
/// where `T_bp` is the bead's committed `weak_target` and `T_net` is the
/// network target from the bead's own header. Because a weak share commits a
/// target weaker than the network's, the ratio lies in `(0, 1)`.
pub fn block_probability_q(bead: &Bead, bead_index: usize) -> Result<u128, EdcaError> {
    let bead_target = bitcoin::Target::from_compact(bead.committed_metadata.weak_target);
    let network_target = bitcoin::Target::from_compact(bead.block_header.bits);
    if bead_target == bitcoin::Target::ZERO {
        return Err(EdcaError::ZeroBeadTarget { bead_index });
    }
    if bead_target <= network_target {
        return Ok(ONE);
    }
    ratio_q(
        &target_to_biguint(network_target),
        &target_to_biguint(bead_target),
        bead_index,
    )
}

/// Computes the raw score `S_i = (D_bp / D_network) * A_i` .
/// # Example
/// ```
/// use node::edca::fixed::{q_to_sats_floor, ONE};
/// use node::edca::score::raw_score;
/// // A bead 1024x easier than the network, on a 3.125 BTC template.
/// // 1/1024 is exact in (u64,u64), so the only rounding is the final floor:
/// // 312_500_000 / 1024 == 305_175.78125 sats of expected value.
/// let probability = ONE / 1024;
/// let score = raw_score(probability, 312_500_000).expect("in range");
/// assert_eq!(q_to_sats_floor(score), 305_175);
/// ```
pub fn raw_score(probability_q: u128, amplifier_sats: u64) -> Result<u128, EdcaError> {
    // A_i lifted into (u64,u64) cannot overflow (u64 << 64 < 2^128), and the
    // split-shift keeps the product exact.
    mul_frac((amplifier_sats as u128) << 64, probability_q)
}

/// Computes the decayed EDCA weight `W_i = S_i * r^{dc_i}` .
pub fn decayed_weight(
    raw_score: u128,
    age_in_cohorts: usize,
    table: &DecayTable,
) -> Result<u128, EdcaError> {
    let multiplier = table.multiplier(age_in_cohorts);
    if multiplier == ONE {
        return Ok(raw_score);
    }
    mul_frac(raw_score, multiplier)
}
