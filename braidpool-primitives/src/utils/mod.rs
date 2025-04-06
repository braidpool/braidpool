// Bitcoin Imports
use ::bitcoin::BlockHash;

// Standard Imports
use std::collections::HashSet;

pub mod bitcoin;

// External Type Aliases
pub type BeadHash = BlockHash;
pub type Byte = u8;
pub type Bytes = Vec<Byte>;

// Internal Type Aliases
pub(crate) type ParentBeadHash = BeadHash;
pub(crate) type ChildrenBeadHash = BeadHash;
pub(crate) type RelativeBeadHash = BeadHash;
pub(crate) type Parents = HashSet<BeadHash>;
pub(crate) type Children = HashSet<BeadHash>;

// Error Definitions
use std::fmt;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BeadLoadError {
    BeadPruned,
    InvalidBeadHash,
    DatabaseError,
}

impl fmt::Display for BeadLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BeadLoadError::BeadPruned => write!(f, "Bead not found"),
            BeadLoadError::InvalidBeadHash => write!(f, "Invalid bead hash"),
            BeadLoadError::DatabaseError => write!(f, "Database error occurred"),
        }
    }
}

impl std::error::Error for BeadLoadError {}