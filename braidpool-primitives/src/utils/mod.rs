// Bitcoin Imports
use ::bitcoin::BlockHash;

// Standard Imports

pub mod bitcoin;
pub mod test_utils;

// External Type Aliases
pub type BeadHash = BlockHash;
pub type Byte = u8;
pub type Bytes = Vec<Byte>;

// Internal Type Aliases
pub(crate) type ParentBeadHash = BeadHash;
pub(crate) type Parents = Vec<ParentBeadHash>;

// Error Definitions
use std::fmt::{self};
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BeadLoadError {
    BeadPruned,
    InvalidBeadHash,
    DatabaseError,
    BeadNotFound,
}

impl fmt::Display for BeadLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BeadLoadError::BeadPruned => write!(f, "Bead has been pruned"),
            BeadLoadError::InvalidBeadHash => write!(f, "Invalid bead hash"),
            BeadLoadError::DatabaseError => write!(f, "Database error occurred"),
            BeadLoadError::BeadNotFound => write!(f, "Bead not found"),
        }
    }
}

impl std::error::Error for BeadLoadError {}
