use std::collections::{BTreeMap, VecDeque};

use crate::braid::Braid;
use crate::edca::decay::DecayTable;
use crate::edca::fixed::{mul_frac, sats_to_q, ONE};
use crate::edca::score::{block_probability_q, fee_amplifier, raw_score, AmplifierSource};
use crate::edca::EdcaConfig;
use crate::error::EdcaError;

/// Unique parameter for mapping weak_shares/beads for each miner representing its
/// `pubkey` committed inside in each bead's committed_metadata specific to swarm.
pub type MinerKey = String;

/// One retained cohort's undecayed per-miner scores.
/// this will keep per cohort state including current cohort age and scores map
/// since the scores for each bead present inside a cohort will remain as it as until pruned beyond
/// dust_limit .
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CohortWeights {
    /// This is cohort's age being used for computing decayed score during block rewards .
    pub ordinal: usize,
    /// Undecayed `S_i` totals per payout address, in (u64,u64).
    ///
    /// A `BTreeMap`, so iteration is in payout-address order on every node.
    pub scores: BTreeMap<MinerKey, u128>,
    /// The undecayed aggregate `sum(S_i)` over this cohort, in (u64,u64).
    pub raw_aggregate: u128,
}

impl CohortWeights {
    /// Returns this cohort's decayed aggregate weight at the given age.
    pub fn decayed_aggregate(
        &self,
        age_in_cohorts: usize,
        table: &DecayTable,
    ) -> Result<u128, EdcaError> {
        // s_i*r^delta_d  = decayed_score .
        let multiplier = table.multiplier(age_in_cohorts);
        if multiplier == ONE {
            return Ok(self.raw_aggregate);
        }
        // sigma s_i * r^delta_d = (tip_cohort_age-current_cohort_age) .
        mul_frac(self.raw_aggregate, multiplier)
    }
}

/// The bounded active EDCA state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EdcaState {
    /// Retained cohorts, oldest at the front, strictly ascending by cohort_age.
    cohorts: VecDeque<CohortWeights>,
    /// Tip cohort age .
    tip_ordinal: usize,
    /// Precomputed `r^delta_age` powers.
    table: DecayTable,
    /// Protocol parameters.
    config: EdcaConfig,
    /// Number of distinct committed `weak_target` values seen while building.
    distinct_bead_targets: usize,
}

impl EdcaState {
    /// Builds the EDCA state from a braid.
    /// Iterating through each cohort of a braid and accumulating complete .
    pub fn from_braid(
        braid: &Braid,
        config: EdcaConfig,
        amplifier: &dyn AmplifierSource,
    ) -> Result<Self, EdcaError> {
        // Fetching the pre-computed decay table .
        let table = DecayTable::new(config.retention_num, config.retention_den)?;
        let mut cohorts: VecDeque<CohortWeights> = VecDeque::new();
        let mut observed_targets: BTreeMap<u32, ()> = BTreeMap::new();
        let mut unscorable_beads: usize = 0;

        // A cohort as old as the decay table has an exactly zero multiplier and
        // would be dropped by `prune` anyway, so it is never scored. That bounds
        // a rebuild by the table length instead of by the whole braid history.
        let first_scored = braid.cohorts.len().saturating_sub(table.len());
        // Skipping non-scorable pruned cohorts .
        for (ordinal, cohort) in braid.cohorts.iter().enumerate().skip(first_scored) {
            let mut bead_indices: Vec<usize> = cohort.0.iter().copied().collect();
            bead_indices.sort_unstable();

            // Undecayed scores for each miner's beads present in each cohort.
            let mut scores: BTreeMap<MinerKey, u128> = BTreeMap::new();
            let mut raw_aggregate: u128 = 0;

            for bead_index in bead_indices {
                let bead = braid
                    .beads
                    .get(bead_index)
                    .ok_or(EdcaError::BeadIndexOutOfRange { index: bead_index })?;
                // Computing probability for each bead for being a mainnet valid block
                // D_bp/D_network = T_network/T_bp in (u64,u64) format .
                let probability = match block_probability_q(bead, bead_index) {
                    Ok(probability) => probability,
                    // Invalid bead .
                    Err(EdcaError::ZeroBeadTarget { .. }) => {
                        unscorable_beads += 1;
                        continue;
                    }
                    Err(error) => return Err(error),
                };

                observed_targets.insert(bead.committed_metadata.weak_target.to_consensus(), ());
                let fees = amplifier.fee_sats(bead)?;
                // Adding base_reward + fees_amplifier = A_i
                let amplifier_sats = fee_amplifier(config.base_subsidy_sats, fees)?;
                // Computing score for each bead not decayed .
                let score = raw_score(probability, amplifier_sats)?;
                // Cumulative undecayed score for each miner added per bead .
                let entry = scores
                    .entry(bead.committed_metadata.payout_address.clone())
                    .or_insert(0);
                *entry = entry.checked_add(score).ok_or(EdcaError::WeightOverflow)?;
                // Total aggregate per cohort .
                raw_aggregate = raw_aggregate
                    .checked_add(score)
                    .ok_or(EdcaError::WeightOverflow)?;
            }

            cohorts.push_back(CohortWeights {
                ordinal,
                scores,
                raw_aggregate,
            });
        }

        let tip_ordinal = braid.cohorts.len().saturating_sub(1);
        if observed_targets.len() > 1 {
            tracing::warn!(
                distinct_weak_targets = observed_targets.len(),
                "EDCA: beads carry more than one distinct weak_target; \
                 docs/EDCA.pdf §III.B assumes a uniform global difficulty D_bp"
            );
        }

        if unscorable_beads > 0 {
            tracing::warn!(
                unscorable_beads,
                "EDCA: skipped beads that commit a zero weak_target"
            );
        }

        let mut state = EdcaState {
            cohorts,
            tip_ordinal,
            table,
            config,
            distinct_bead_targets: observed_targets.len(),
        };
        state.prune()?;
        Ok(state)
    }

    /// Returns the truncation threshold `L_dust * (1 - r)`, in (u64,u64) format.
    /// corresponding to decaying retention and the dust_limit set in edca_config .
    pub fn truncation_threshold(&self) -> Result<u128, EdcaError> {
        mul_frac(
            sats_to_q(self.config.dust_limit_sats),
            ONE - self.table.retention(),
        )
    }

    /// Returns the topological age `dc` of a cohort, in elapsed cohorts.
    /// used for decaying the undecayed bead_score.
    pub fn age_of(&self, ordinal: usize) -> usize {
        self.tip_ordinal.saturating_sub(ordinal)
    }

    /// Advances the state to a new tip cohort ordinal and re-prunes.
    pub fn advance_to(&mut self, tip_ordinal: usize) -> Result<(), EdcaError> {
        self.tip_ordinal = tip_ordinal;
        self.prune()
    }

    /// Drops every retained cohort that fails either ceiling:
    ///
    /// 1. its decayed aggregate has fallen below `L_dust * (1 - r)`, or
    /// 2. its age has passed the end of the decay table, where `r^age` has
    ///    underflowed to exactly zero.
    pub fn prune(&mut self) -> Result<(), EdcaError> {
        let threshold = self.truncation_threshold()?;
        let table_len = self.table.len();
        let tip_ordinal = self.tip_ordinal;
        let table = &self.table;

        // Removing cohorts falling below threshold .
        let mut retained: VecDeque<CohortWeights> = VecDeque::with_capacity(self.cohorts.len());
        for cohort in self.cohorts.drain(..) {
            let age = tip_ordinal.saturating_sub(cohort.ordinal);
            if age >= table_len {
                continue;
            }
            if cohort.decayed_aggregate(age, table)? < threshold {
                continue;
            }
            retained.push_back(cohort);
        }
        self.cohorts = retained;
        Ok(())
    }

    /// Computes each miner's total decayed weight `U_m = sum_{i in m} W_i`.
    pub fn miner_totals(&self) -> Result<BTreeMap<MinerKey, u128>, EdcaError> {
        let mut totals: BTreeMap<MinerKey, u128> = BTreeMap::new();
        for cohort in &self.cohorts {
            let age = self.age_of(cohort.ordinal);
            let multiplier = self.table.multiplier(age);
            if multiplier == 0 {
                continue;
            }
            for (miner, score) in &cohort.scores {
                let weight = if multiplier == ONE {
                    *score
                } else {
                    mul_frac(*score, multiplier)?
                };
                let entry = totals.entry(miner.clone()).or_insert(0);
                *entry = entry.checked_add(weight).ok_or(EdcaError::WeightOverflow)?;
            }
        }
        Ok(totals)
    }

    /// Computes the active global pool weight `U_total = sum_m `.
    pub fn total_weight(totals: &BTreeMap<MinerKey, u128>) -> Result<u128, EdcaError> {
        let mut total: u128 = 0;
        for weight in totals.values() {
            total = total
                .checked_add(*weight)
                .ok_or(EdcaError::WeightOverflow)?;
        }
        Ok(total)
    }

    /// Returns the retained cohorts, oldest first.
    pub fn cohorts(&self) -> &VecDeque<CohortWeights> {
        &self.cohorts
    }

    /// Returns the ordinal of the newest ingested cohort.
    pub fn tip_ordinal(&self) -> usize {
        self.tip_ordinal
    }

    /// Returns the decay table backing this state.
    pub fn table(&self) -> &DecayTable {
        &self.table
    }

    /// Returns the protocol parameters this state was built with.
    pub fn config(&self) -> &EdcaConfig {
        &self.config
    }

    /// Returns how many distinct committed `weak_target` values were observed.
    pub fn distinct_bead_targets(&self) -> usize {
        self.distinct_bead_targets
    }
}
