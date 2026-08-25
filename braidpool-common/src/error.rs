use bitcoin::{bech32, witness_program};
use core::fmt;

/// Error type for parsing cpunet from string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseCpunetError(pub String);

impl fmt::Display for ParseCpunetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to parse '{}' as cpunet", self.0)
    }
}

impl std::error::Error for ParseCpunetError {}

/// Error type for cpunet address operations.
#[derive(Debug, Clone)]
pub enum CpunetAddressError {
    /// Bech32 decoding error
    Bech32(bech32::segwit::DecodeError),
    /// Wrong network HRP
    WrongNetwork { expected: String, found: String },
    /// Invalid witness version
    InvalidWitnessVersion(u8),
    /// Invalid witness program
    InvalidProgram(witness_program::Error),
}

impl fmt::Display for CpunetAddressError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bech32(e) => write!(f, "bech32 decode error: {}", e),
            Self::WrongNetwork { expected, found } => {
                write!(
                    f,
                    "wrong network: expected '{}', found '{}'",
                    expected, found
                )
            }
            Self::InvalidWitnessVersion(v) => write!(f, "invalid witness version: {}", v),
            Self::InvalidProgram(e) => write!(f, "invalid witness program: {}", e),
        }
    }
}

impl std::error::Error for CpunetAddressError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Bech32(e) => Some(e),
            Self::InvalidProgram(e) => Some(e),
            _ => None,
        }
    }
}
