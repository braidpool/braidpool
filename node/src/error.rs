//All braidpool specific errors are defined here
use std::fmt;

#[derive(Debug)]
//Custom error class for handling all the braid consensus errors
pub enum BraidError {
    MissingAncestorWork,
    HighestWorkBeadFetchFailed,
}
#[derive(Debug)]
pub enum BraidRPCError {
    RequestFailed {
        method: String,
        source: jsonrpsee::core::ClientError,
    },
}
#[derive(Debug)]
pub enum IPCtemplateError {
    TemplateConsumError,
}
impl fmt::Display for BraidRPCError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BraidRPCError::RequestFailed { method, source } => {
                write!(
                    f,
                    "{} error occurred while sending {} request to the server",
                    method, source
                )
            }
        }
    }
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
impl fmt::Display for IPCtemplateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IPCtemplateError::TemplateConsumError => {
                write!(f, "An error occurred while consuming the template")
            }
        }
    }
}
impl std::error::Error for BraidError {}
