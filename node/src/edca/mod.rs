pub mod decay;
pub mod fixed;
pub mod payout;
pub mod score;
pub mod settle;
pub mod state;
pub mod validate_fees;

use crate::config::PoolNetwork;
use bitcoin::Network;

pub use decay::{DecayTable, MAX_DECAY_TABLE_LEN};
pub use score::{AmplifierSource, CommittedFeeAmplifier, SubsidyOnlyAmplifier, VerdictAmplifier};
pub use settle::{settle, settle_totals, PayoutEntity, PayoutEntry};
pub use state::{CohortWeights, EdcaState, MinerKey};
pub use validate_fees::{
    compute_block_fees, root_from_branch, transaction_fee, verify_fee_against_template,
    verify_fee_bound, verify_fee_commitment, BranchKey, ChainAnchor, FeeBound, FeeCommitment,
    FeeVerdict, FeeVerdictSource, PrevoutSource, TemplateCache, TemplateEntry, TransactionFee,
    TxFeeSource,
};

/// Protocol parameters for the EDCA payout engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EdcaConfig {
    /// Numerator of the retention multiplier `r`.
    pub retention_num: u64,
    /// Denominator of the retention multiplier `r`. Must exceed the numerator.
    pub retention_den: u64,
    /// The Bitcoin dust limit `L_dust` in satoshis.
    pub dust_limit_sats: u64,
    /// `B_base`, the fixed block subsidy for the current halving epoch
    /// in satoshis.
    pub base_subsidy_sats: u64,
}

/// Default retention multiplier numerator .
pub const DEFAULT_RETENTION_NUM: u64 = 80;

/// Default retention multiplier denominator .
pub const DEFAULT_RETENTION_DEN: u64 = 100;

/// Default dust limit `L_dust`, in satoshis.
pub const DEFAULT_DUST_LIMIT_SATS: u64 = 546;

/// Default block subsidy `B_base` .
pub const DEFAULT_BASE_SUBSIDY_SATS: u64 = 312_500_000;

impl Default for EdcaConfig {
    fn default() -> Self {
        Self {
            retention_num: DEFAULT_RETENTION_NUM,
            retention_den: DEFAULT_RETENTION_DEN,
            dust_limit_sats: DEFAULT_DUST_LIMIT_SATS,
            base_subsidy_sats: DEFAULT_BASE_SUBSIDY_SATS,
        }
    }
}

/// Block subsidy `B_base` in force on regtest and cpunet, in satoshis (50 BTC).
pub const REGTEST_BASE_SUBSIDY_SATS: u64 = 5_000_000_000;

impl EdcaConfig {
    /// Returns the parameters for a live pool on `network`.
    pub fn for_network(network: PoolNetwork) -> Self {
        // Regtest and cpunet both start from the genesis subsidy schedule and
        // in practice never reach a halving during a test run.
        let base_subsidy_sats = match network {
            PoolNetwork::Cpunet | PoolNetwork::Bitcoin(Network::Regtest) => {
                REGTEST_BASE_SUBSIDY_SATS
            }
            PoolNetwork::Bitcoin(_) => DEFAULT_BASE_SUBSIDY_SATS,
        };
        Self {
            base_subsidy_sats,
            ..Self::default()
        }
    }
}
