use crate::edca::fixed::{FRAC_BITS, ONE};
use crate::error::EdcaError;

/// Hard ceiling on the number of entries in a [`DecayTable`].
/// TODO: Setting up the a more righter bound for the table size .
pub const MAX_DECAY_TABLE_LEN: usize = 8192;

/// Precomputed powers of the retention multiplier `r`, in (u64,u64).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecayTable {
    /// `powers[k] == r^k` in (u64,u64). `powers[0] == ONE`.
    powers: Vec<u128>,
    /// The retention multiplier `r` itself, in (u64,u64).
    retention: u128,
}

impl DecayTable {
    /// Builds the decay table for the exact rational retention multiplier
    /// `numerator / denominator`.
    pub fn new(numerator: u64, denominator: u64) -> Result<Self, EdcaError> {
        if numerator == 0 || denominator == 0 || numerator >= denominator {
            return Err(EdcaError::InvalidRetention {
                numerator,
                denominator,
            });
        }
        let retention = ((numerator as u128) << FRAC_BITS) / (denominator as u128);
        let mut powers = Vec::with_capacity(64);
        powers.push(ONE);
        while powers.len() < MAX_DECAY_TABLE_LEN {
            let previous = match powers.last() {
                Some(value) => *value,
                None => return Err(EdcaError::FixedPointOverflow),
            };
            let next = previous
                .checked_mul(numerator as u128)
                .ok_or(EdcaError::FixedPointOverflow)?
                / (denominator as u128);
            if next == 0 {
                // r^k has underflowed below one (u64,u64); every older cohort
                // has an exactly zero multiplier.
                break;
            }
            powers.push(next);
        }
        Ok(DecayTable { powers, retention })
    }

    /// Returns the decay multiplier `r^age` in (u64,u64).
    pub fn multiplier(&self, age: usize) -> u128 {
        self.powers.get(age).copied().unwrap_or(0)
    }

    /// Returns the retention multiplier `r` itself, in (u64,u64).
    pub fn retention(&self) -> u128 {
        self.retention
    }

    /// Returns the number of ages with a non-zero multiplier.
    pub fn len(&self) -> usize {
        self.powers.len()
    }

    /// Returns whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.powers.is_empty()
    }
}
