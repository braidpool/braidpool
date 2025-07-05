use std::fmt;

#[derive(Debug)]
//Custom error class for handling all the braid consensus errors
pub enum BraidError {
    MissingAncestorWork,
    HighestWorkBeadFetchFailed,
}

impl fmt::Display for BraidError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BraidError::MissingAncestorWork => write!(f, "Missing ancestor work map"),
            BraidError::HighestWorkBeadFetchFailed => {
                write!(f, "An error occurred while fetching the highest work bead")
            }
        }
    }
}

impl std::error::Error for BraidError {}
