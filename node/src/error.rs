//All braidpool specific errors are defined here
use std::fmt;

use crate::stratum::{BlockTemplate, JobDetails};
use bitcoin::address::ParseError as AddressParseError;
use tokio::sync::oneshot;

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
    TemplateConsumeError,
}
#[derive(Debug, Clone)]
pub enum BraidpoolError {
    QueueFull { queue_type: String },
}
pub enum ErrorKind {
    Temporary,
    ConnectionBroken,
    LogicError,
}
#[derive(Debug)]
pub enum StratumErrors {
    InvalidMethod {
        method: String,
    },
    InvalidMethodParams {
        method: String,
    },
    MiningJobNotFound {
        job_id: u64,
    },
    MiningJobInsertError {
        mining_job: JobDetails,
    },
    JobNotificationNotConstructed {
        job_template: BlockTemplate,
    },
    ResponseWriteError {
        error: std::io::Error,
    },
    InvalidCoinbase,
    PeerNotFoundInConnectionMapping {
        peer_addr: String,
    },
    UnableToReadStream {
        error: tokio_util::codec::LinesCodecError,
    },
    ParamNotFound {
        param: String,
        method: String,
    },
    JobIdCouldNotBeParsed {
        method: String,
        error: String,
    },
    ConfigureFeatureStringConversion {
        error: String,
    },
    VersionRollingStringParseError {
        error: String,
    },
    VersionRollingHexParseError {
        error: String,
    },
    VersionrollingMinBitCountHexParseError {
        error: String,
    },
    NotifyMessageNotSent {
        error: String,
        msg: String,
        msg_type: String,
    },
    ParsingVersionMask {
        error: String,
    },
    MaskNotValid {
        error: String,
    },
    PrevHashNotReversed {
        error: String,
    },
    CandidateBlockNotSent {
        error: String,
    },
    ErrorFetchingCurrentUNIXTimestamp {
        error: String,
    },
}
pub enum StratumResponseErrors {}
impl fmt::Display for StratumErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StratumErrors::ErrorFetchingCurrentUNIXTimestamp { error } => {
                write!(
                    f,
                    "An error {:?} occurred while getting the current unix timestamp .",
                    error
                )
            }
            StratumErrors::CandidateBlockNotSent { error } => {
                write!(f, "{:?}", error)
            }
            StratumErrors::PrevHashNotReversed { error } => {
                write!(
                    f,
                    "An error occurred while reversing the prev hash in 4 word size length - {}",
                    error
                )
            }
            StratumErrors::MaskNotValid { error } => {
                write!(f, "{}", error)
            }
            StratumErrors::ParsingVersionMask { error } => {
                write!(f, "{}", error)
            }
            StratumErrors::NotifyMessageNotSent {
                error,
                msg,
                msg_type,
            } => {
                write!(
                    f,
                    "{} occurred while sending the following message - {} to downstream node in message type - {}",
                    error, msg,msg_type
                )
            }
            StratumErrors::VersionrollingMinBitCountHexParseError { error } => {
                write!(
                    f,
                    "{} occurred while parsing Version rolling min bit in mining.configure",
                    error
                )
            }
            StratumErrors::VersionRollingStringParseError { error } => {
                write!(
                    f,
                    "{} occurred while parsing the version rolling to string type",
                    error
                )
            }
            StratumErrors::VersionRollingHexParseError { error } => {
                write!(
                    f,
                    "{} occurred while parsing Version rolling in mining.configure",
                    error
                )
            }
            StratumErrors::ConfigureFeatureStringConversion { error } => {
                write!(f, "{}", error)
            }
            StratumErrors::JobIdCouldNotBeParsed { method, error } => {
                write!(
                    f,
                    "Job id could not be parsed due to the error - {} in the method - {}",
                    error, method
                )
            }
            StratumErrors::ParamNotFound { param, method } => {
                write!(
                    f,
                    "Required param {} for the following method {} not found ",
                    param, method
                )
            }
            StratumErrors::UnableToReadStream { error } => {
                write!(f, "Unable to fetch stream - {}", error)
            }
            StratumErrors::PeerNotFoundInConnectionMapping { peer_addr } => {
                write!(
                    f,
                    "The following peer with socket addr {:?} not found in the connection mapping ",
                    peer_addr
                )
            }
            StratumErrors::InvalidCoinbase => {
                write!(f, "Provided coinbase is invalid")
            }
            StratumErrors::ResponseWriteError { error } => {
                write!(f, "{:?}", error)
            }
            StratumErrors::JobNotificationNotConstructed { job_template } => {
                write!(
                    f,
                    "The job notification for the given template could not be constructed - {:?}",
                    job_template
                )
            }
            StratumErrors::InvalidMethod { method } => {
                write!(
                    f,
                    "Invalid method received from downstream namely - {:?}",
                    method
                )
            }
            StratumErrors::InvalidMethodParams { method } => {
                write!(
                    f,
                    "Invalid params passed to the stratum method - {:?}",
                    method
                )
            }
            StratumErrors::MiningJobNotFound { job_id } => {
                write!(
                    f,
                    "No mining job found with the provided job id - {:?}",
                    job_id
                )
            }
            StratumErrors::MiningJobInsertError { mining_job } => {
                write!(f,"An error occurred while inserting the following job into the mining map - {:?}",mining_job)
            }
        }
    }
}

/// Determines if an error indicates a connection/communication failure
///
/// This function classifies errors to distinguish between:
/// * Connection errors: Require reconnection, no point in retrying
/// * Logic errors: May succeed on retry (temporary issues)
pub fn classify_error(error: &Box<dyn std::error::Error>) -> ErrorKind {
    if let Some(io_err) = error.downcast_ref::<std::io::Error>() {
        match io_err.kind() {
            std::io::ErrorKind::ConnectionReset
            | std::io::ErrorKind::ConnectionAborted
            | std::io::ErrorKind::BrokenPipe
            | std::io::ErrorKind::NotConnected => return ErrorKind::ConnectionBroken,

            std::io::ErrorKind::TimedOut
            | std::io::ErrorKind::Interrupted
            | std::io::ErrorKind::WouldBlock => return ErrorKind::Temporary,

            _ => {}
        }
    }

    if error.downcast_ref::<oneshot::error::RecvError>().is_some() {
        return ErrorKind::ConnectionBroken;
    }

    let error_str = error.to_string().to_lowercase();

    if [
        "connection refused",
        "connection reset",
        "connection lost",
        "broken pipe",
        "no such file",
        "permission denied",
        "disconnected",
        "bootstrap failed, remote exception",
        "Method not implemented",
    ]
    .iter()
    .any(|keyword| error_str.contains(keyword))
    {
        return ErrorKind::ConnectionBroken;
    }

    if [
        "timeout",
        "try again",
        "temporary",
        "interrupted",
        "busy",
        "unavailable",
        "overloaded",
    ]
    .iter()
    .any(|keyword| error_str.contains(keyword))
    {
        return ErrorKind::Temporary;
    }

    // Default to logic error
    ErrorKind::LogicError
}

impl fmt::Display for BraidpoolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BraidpoolError::QueueFull { queue_type } => write!(f, "{} queue is full", queue_type),
        }
    }
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
            IPCtemplateError::TemplateConsumeError => {
                write!(f, "An error occurred while consuming the template")
            }
        }
    }
}
impl std::error::Error for BraidError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoinbaseError {
    InvalidExtranonceLength,
    InvalidBitcoinAddress(String),
    AddressNetworkMismatch,
    ScriptCreationError,
    InvalidBlockTemplateData,
    ConsensusDecodeError,
    InvalidCommitmentLength,
    OpReturnTooLarge,
    PushBytesError(bitcoin::script::PushBytesError),
    AddressError(AddressParseError),
    TemplateMissingOutputs,
}

impl fmt::Display for CoinbaseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoinbaseError::InvalidExtranonceLength => write!(f, "Invalid extranonce length"),
            CoinbaseError::InvalidBitcoinAddress(addr) => {
                write!(f, "Invalid Bitcoin address: {}", addr)
            }
            CoinbaseError::AddressNetworkMismatch => {
                write!(f, "Address is not for the Bitcoin network")
            }
            CoinbaseError::ScriptCreationError => write!(f, "Failed to create script"),
            CoinbaseError::InvalidBlockTemplateData => write!(f, "Invalid block template data"),
            CoinbaseError::ConsensusDecodeError => write!(f, "Failed to decode transaction"),
            CoinbaseError::InvalidCommitmentLength => write!(f, "Invalid commitment length"),
            CoinbaseError::OpReturnTooLarge => write!(f, "OP_RETURN data exceeds 80 bytes"),
            CoinbaseError::PushBytesError(e) => write!(f, "Push bytes error: {}", e),
            CoinbaseError::AddressError(e) => write!(f, "Address error: {}", e),
            CoinbaseError::TemplateMissingOutputs => {
                write!(f, "Original coinbase template is missing expected outputs")
            }
        }
    }
}

impl std::error::Error for CoinbaseError {}
