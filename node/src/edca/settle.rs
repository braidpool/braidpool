//! On-chain settlement: payout shares, dust aggregation and redistribution.

use std::collections::BTreeMap;

use num::{BigUint, ToPrimitive};

use crate::edca::state::{EdcaState, MinerKey};
use crate::error::EdcaError;

/// One miner's settled on-chain output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayoutEntry {
    /// The miner's committed `payout_address`.
    pub address: MinerKey,
    /// The final adjusted payout `O'_q`, in satoshis.
    pub value_sats: u64,
    /// The miner's total decayed weight `U_m`.
    pub weight: u128,
}

/// The complete settled payout set for one block.
/// storing each payout per miner mapped for each dust value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayoutEntity {
    /// Qualifying outputs, in payout-address order.
    pub entries: Vec<PayoutEntry>,
    /// `A_total`, the amount the entries sum to, in satoshis.
    pub total_sats: u64,
    /// `D_total`, the aggregated sub-dust value that was swept and
    /// redistributed, in satoshis.
    pub swept_dust_sats: u64,
    /// Number of miners whose nominal output fell below `L_dust` and were
    /// therefore stripped from the roster.
    pub dust_miner_count: usize,
}

impl PayoutEntity {
    /// Verifies that the roster's outputs sum to exactly `total_sats`.
    pub fn validate(&self) -> Result<(), EdcaError> {
        let mut sum: u64 = 0;
        for entry in &self.entries {
            sum = sum
                .checked_add(entry.value_sats)
                .ok_or(EdcaError::WeightOverflow)?;
        }
        if sum != self.total_sats {
            return Err(EdcaError::RosterSumMismatch {
                roster_total: sum,
                expected_total: self.total_sats,
            });
        }
        Ok(())
    }
}

/// Computes the nominal outputs `O_m = P_m * A_total` of
/// closed to sum exactly to `A_total`.
pub fn nominal_outputs(
    totals: &BTreeMap<MinerKey, u128>,
    total_sats: u64,
) -> Result<BTreeMap<MinerKey, u64>, EdcaError> {
    let pool_weight = EdcaState::total_weight(totals)?;
    if pool_weight == 0 || totals.is_empty() {
        return Err(EdcaError::EmptyState);
    }

    let mut outputs: BTreeMap<MinerKey, u64> = BTreeMap::new();
    let mut remainders: Vec<(u128, MinerKey)> = Vec::with_capacity(totals.len());
    let mut allocated: u64 = 0;

    for (miner, weight) in totals {
        let numerator = BigUint::from(*weight) * BigUint::from(total_sats);
        let pool = BigUint::from(pool_weight);
        let share = (&numerator / &pool)
            .to_u64()
            .ok_or(EdcaError::FixedPointOverflow)?;
        let remainder = (&numerator % &pool)
            .to_u128()
            .ok_or(EdcaError::FixedPointOverflow)?;
        allocated = allocated
            .checked_add(share)
            .ok_or(EdcaError::WeightOverflow)?;
        outputs.insert(miner.clone(), share);
        remainders.push((remainder, miner.clone()));
    }

    // Largest remainder first; ties broken by address ascending.
    remainders.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1)));

    let mut leftover = total_sats.saturating_sub(allocated);
    for (_, miner) in remainders.iter() {
        if leftover == 0 {
            break;
        }
        if let Some(value) = outputs.get_mut(miner) {
            *value = value.checked_add(1).ok_or(EdcaError::WeightOverflow)?;
            leftover -= 1;
        }
    }

    Ok(outputs)
}

/// Splits the nominal outputs into the dust set and the active set of
/// and aggregates the dust.
pub fn partition_dust(
    outputs: &BTreeMap<MinerKey, u64>,
    dust_limit_sats: u64,
) -> Result<(BTreeMap<MinerKey, u64>, BTreeMap<MinerKey, u64>, u64), EdcaError> {
    let mut active: BTreeMap<MinerKey, u64> = BTreeMap::new();
    let mut dust: BTreeMap<MinerKey, u64> = BTreeMap::new();
    let mut dust_total: u64 = 0;

    for (miner, value) in outputs {
        if *value < dust_limit_sats {
            dust_total = dust_total
                .checked_add(*value)
                .ok_or(EdcaError::WeightOverflow)?;
            dust.insert(miner.clone(), *value);
        } else {
            active.insert(miner.clone(), *value);
        }
    }

    Ok((active, dust, dust_total))
}

/// Redistributes the aggregated dust across the qualifying set.
///
/// Computes
///
/// ```text
/// O'_q = O_q + (O_q / sum_{j in M_active} O_j) * D_total
/// ```
///
/// in exact integer arithmetic, then closes the floor remainder by largest
/// fractional remainder (ties by address ascending) so that the adjusted
/// outputs sum to exactly `sum_active + D_total`,is explicit that the
/// dust is *not* claimed as a fee by the block finder, so it can only go to the
/// qualifying miners.
///
/// Redistribution only ever adds to an output, so no `O'_q` can fall back below
/// `L_dust`; a single pass suffices.
pub fn redistribute_dust(
    active: &BTreeMap<MinerKey, u64>,
    dust_total: u64,
) -> Result<BTreeMap<MinerKey, u64>, EdcaError> {
    let mut active_sum: u64 = 0;
    for value in active.values() {
        active_sum = active_sum
            .checked_add(*value)
            .ok_or(EdcaError::WeightOverflow)?;
    }
    if active.is_empty() || active_sum == 0 {
        return Err(EdcaError::EmptyState);
    }
    if dust_total == 0 {
        return Ok(active.clone());
    }

    let denominator = active_sum as u128;
    let mut adjusted: BTreeMap<MinerKey, u64> = BTreeMap::new();
    let mut remainders: Vec<(u128, MinerKey)> = Vec::with_capacity(active.len());
    let mut allocated_dust: u64 = 0;

    for (miner, value) in active {
        let numerator = (*value as u128)
            .checked_mul(dust_total as u128)
            .ok_or(EdcaError::WeightOverflow)?;
        // This is done to preserve the proportion of shares in whole number format
        // whereas the leftover sum comes out as summation of remainders which is again distributed
        // according to the ordering of largest remainder to lowest until any leftover is left
        // to be committed per miner's amount to be committed inside the coinbase_transaction .
        let quotient = numerator / denominator;
        let remainder = numerator % denominator;
        let bonus = u64::try_from(quotient).map_err(|_| EdcaError::WeightOverflow)?;
        allocated_dust = allocated_dust
            .checked_add(bonus)
            .ok_or(EdcaError::WeightOverflow)?;
        adjusted.insert(
            miner.clone(),
            value.checked_add(bonus).ok_or(EdcaError::WeightOverflow)?,
        );
        remainders.push((remainder, miner.clone()));
    }
    // Sorting remainders being contributed by the miners from largest to smallest .
    remainders.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1)));

    // Updating the whole allocation for each miner according to left-over .
    let mut leftover = dust_total.saturating_sub(allocated_dust);
    for (_, miner) in remainders.iter() {
        if leftover == 0 {
            break;
        }
        if let Some(value) = adjusted.get_mut(miner) {
            *value = value.checked_add(1).ok_or(EdcaError::WeightOverflow)?;
            leftover -= 1;
        }
    }
    Ok(adjusted)
}

/// Settles a block reward into a zero-sum payout roster.
pub fn settle(state: &EdcaState, total_sats: u64) -> Result<PayoutEntity, EdcaError> {
    let totals = state.miner_totals()?;
    settle_totals(&totals, total_sats, state.config().dust_limit_sats)
}

/// Settles a block reward against an explicit per-miner weight map.
///
/// Identical to [`settle`] but driven by a caller-supplied `U_m` map rather
/// than the whole state. This is what lets the coinbase builder drop miners it
/// cannot pay — an unresolvable payout address, or a miner past the coinbase
/// output budget — before the reward is divided. Removing a miner from the map
/// removes them from `U_total` too, so the survivors renormalise instead of the
/// dropped value being destroyed.
pub fn settle_totals(
    totals: &BTreeMap<MinerKey, u128>,
    total_sats: u64,
    dust_limit_sats: u64,
) -> Result<PayoutEntity, EdcaError> {
    // Accumulating payouts wuth complete set including active as well as non-active set .
    let nominal = nominal_outputs(totals, total_sats)?;
    // Splitting into active and non-active or dust set based on the total accumulation comparison
    // with respect to dust limit set as per edca_config .
    let (active, dust, dust_total) = partition_dust(&nominal, dust_limit_sats)?;
    // In case all are below the dust threshold .
    let (final_outputs, dust_miner_count) = if active.is_empty() {
        // TODO: Better approach for pre-allocation to take place here .
        // Degenerate case: award everything to the highest-weight miner.
        let mut best: Option<(&MinerKey, u128)> = None;
        for (miner, weight) in totals {
            let take = match best {
                None => true,
                // Strictly greater weight wins; equal weights keep the
                // lexicographically smaller address, which `BTreeMap` order
                // means is the one already held.
                Some((_, best_weight)) => *weight > best_weight,
            };
            if take {
                best = Some((miner, *weight));
            }
        }
        let (winner, _) = best.ok_or(EdcaError::EmptyState)?;
        let mut single: BTreeMap<MinerKey, u64> = BTreeMap::new();
        single.insert(winner.clone(), total_sats);
        (single, dust.len())
    } else {
        // Along with the active set of distribution for each miner
        // redistributing dust on the basis of proportion of (O_q+Sigma O_m for each m belonging in active set / O_total*D_total).
        (redistribute_dust(&active, dust_total)?, dust.len())
    };

    let mut entries: Vec<PayoutEntry> = Vec::with_capacity(final_outputs.len());
    for (miner, value) in &final_outputs {
        entries.push(PayoutEntry {
            address: miner.clone(),
            value_sats: *value,
            weight: totals.get(miner).copied().unwrap_or(0),
        });
    }
    // Forming final Payout to be committed inside coinbase transaction before forwarding
    // template to each miner .
    let roster = PayoutEntity {
        entries,
        total_sats,
        swept_dust_sats: dust_total,
        dust_miner_count,
    };
    roster.validate()?;
    Ok(roster)
}
