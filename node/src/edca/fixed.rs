//! (u64,u64) integer fixed-point arithmetic for EDCA.
//!
//! The only non-`u128` arithmetic in this module is [`num::BigUint`], used
//! solely to divide two 256-bit Bitcoin targets in [`ratio_q`]. `BigUint` is
//! exact integer arithmetic, not floating point.

use crate::error::EdcaError;
use num::BigUint;

/// One, in (u64,u64) format.
pub const ONE: u128 = 1u128 << 64;

/// Mask selecting the 64 fractional bits of a (u64,u64) value.
pub const FRAC_MASK: u128 = ONE - 1;

/// Number of fractional bits in the (u64,u64) representation.
pub const FRAC_BITS: u32 = 64;

/// Multiplies a (u64,u64) value by a (u64,u64) fraction.
///
/// Computes `a * f >> 64` by splitting `a` into independent high and low
/// 64-bit segments, so the 192-bit intermediate product never has to exist in a
/// `u128`. Multiplying a raw score by a shift multiplier directly would let the
/// intermediate silently overflow under an extreme transaction-fee anomaly,
/// artificially capping the score of large miners and destroying Sybil
/// resistance. A saturating or wrapping multiply is therefore *not* an
/// acceptable mitigation here: both partial products are checked and any
/// overflow becomes a typed error.
pub fn mul_frac(a: u128, f: u128) -> Result<u128, EdcaError> {
    // `a` will be representing both fractional as well as integral portion
    // with integral portion represented inside the high/upper postion and the fractional
    // part in lower half position .
    // `f` will be `r` decaying factor lying between 0 and 1 hence the upper part will remain 0
    // so only 64 bits in the lower half is required for the fixed point multiplication to take place
    // and will remain < u64 .

    // Overflow case .
    if f > ONE {
        return Err(EdcaError::FractionOutOfRange { raw: f });
    }
    // `hi` is the integral part of `a`, `lo` its fractional part.
    // by moving 64 bits left and remaining remaining to be formed
    // by applying bitmask of `FRAC_MASK` .

    let hi = a >> FRAC_BITS;
    let lo = a & FRAC_MASK;

    // `lo * f` cannot overflow: lo <= 2^64 - 1 and f <= 2^64, so the product is
    // strictly below 2^128.

    let lo_term = (lo * f) >> FRAC_BITS;

    // `hi * f` is checked: it fits whenever the result itself is representable.
    // this in itself cannot overflow as both hi and f <= 2^64 and no shift is required
    // because integral portion is only there .
    let hi_term = hi.checked_mul(f).ok_or(EdcaError::FixedPointOverflow)?;

    // in `hi_term` the left 64 bits are unset bits and therefore the checked_add will
    // allow the fractional part in `lo_term` to be represented via addition .
    hi_term
        .checked_add(lo_term)
        .ok_or(EdcaError::FixedPointOverflow)
}

/// Converts a satoshi amount into (u64,u64).
pub fn sats_to_q(s: u64) -> u128 {
    (s as u128) << FRAC_BITS
}

/// Converts a (u64,u64) value down to whole satoshis, rounding toward zero.
pub fn q_to_sats_floor(q: u128) -> u64 {
    (q >> FRAC_BITS) as u64
}

/// Builds the (u64,u64) representation of the exact rational `numerator /
/// denominator`, for 256-bit Bitcoin targets.
///
/// The division is performed in [`BigUint`] because Bitcoin
/// targets are 256-bit and do not fit a `u128`; the result is then narrowed
/// back into (u64,u64).
pub fn ratio_q(
    numerator: &BigUint,
    denominator: &BigUint,
    bead_index: usize,
) -> Result<u128, EdcaError> {
    // Additional check for 0 target corresponding to a bead .
    if denominator == &BigUint::from(0u8) {
        return Err(EdcaError::ZeroBeadTarget { bead_index });
    }
    // Representation in terms of (u64_u64) .
    let scaled = (numerator << FRAC_BITS) / denominator;
    let digits = scaled.to_u64_digits();
    // A (u64,u64) value occupies at most two 64-bit digits.
    if digits.len() > 2 {
        return Err(EdcaError::InvalidTargetRatio { bead_index });
    }
    let mut raw: u128 = 0;
    for (position, digit) in digits.iter().enumerate() {
        raw |= (*digit as u128) << (64 * position);
    }
    if raw > ONE {
        return Err(EdcaError::InvalidTargetRatio { bead_index });
    }
    Ok(raw)
}

/// Reads a 256-bit Bitcoin target into a [`BigUint`].
pub fn target_to_biguint(target: bitcoin::Target) -> BigUint {
    BigUint::from_bytes_be(&target.to_be_bytes())
}
