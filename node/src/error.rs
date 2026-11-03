//All braidpool specific errors are defined here
use crate::stratum::{BlockTemplate, JobDetails};
use crate::utils::BeadHash;
use crate::TemplateId;
use bitcoin::address::ParseError as AddressParseError;
use std::{fmt, path::PathBuf};
use tokio::sync::oneshot;

#[derive(Debug)]
//Custom error class for handling all the braid consensus errors
pub enum BraidError {
    MissingAncestorWork,
    HighestWorkBeadFetchFailed,
    /// A bead's committed parent hash is not present in the braid index. This is
    /// a consensus/DAG invariant violation: a connected bead must have all of
    /// its parents resolvable.
    MissingParent {
        bead: BeadHash,
        parent: BeadHash,
    },
    /// A bead is not present in the braid index when persistence was attempted,
    /// despite the braid reporting it as added. Indicates a consensus/logic bug.
    BeadNotIndexed {
        bead: BeadHash,
    },
    /// The bead was resolved but the db channel closed due to an error
    PersistenceChannelClosed {
        bead: BeadHash,
    },
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
#[derive(Debug, Clone)]
pub enum DBErrors {
    TupleNotInserted {
        error: String,
    },
    TupleNotFetched {
        error: String,
    },
    InsertionTransactionNotCommitted {
        error: String,
        query_name: String,
    },
    FetchTransactionNotCommitted {
        error: String,
        query_name: String,
    },
    ConnectionToDBNotEstablished {
        error: String,
    },
    TransactionNotRolledBack {
        error: String,
        query: String,
    },
    TupleAttributeParsingError {
        error: String,
        attribute: String,
    },
    EnvVariableNotFetched {
        error: String,
        var: String,
    },
    DBDirectoryNotCreated {
        error: String,
        path: PathBuf,
    },
    ConnectionToSQlitePoolFailed {
        error: String,
    },
    SchemaNotInitialized {
        error: String,
        db_path: PathBuf,
    },
    SchemaPathNotFound {
        error: String,
        schema_desired_path: PathBuf,
    },
    ConnectionUrlNotParsed {
        error: String,
        url: String,
    },
}
impl fmt::Display for DBErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DBErrors::ConnectionUrlNotParsed { error, url } => {
                write!(f,"Connection URL - {:?} could not be parsed for building connection configuration and initializing connection due to - {:?}",url,error)
            }
            DBErrors::SchemaPathNotFound {
                error,
                schema_desired_path,
            } => {
                write!(
                    f,
                    "Schema could not be read to string due to - {:?} from the path - {:?}",
                    error, schema_desired_path
                )
            }
            DBErrors::SchemaNotInitialized { error, db_path } => {
                write!(f,"Connection to DB initialized but schema could not be executed at the given DB path {:?} due to - {:?}",db_path,error.to_string())
            }
            DBErrors::ConnectionToSQlitePoolFailed { error } => {
                write!(f,"Connection to pool could not be initialized hence DB connection could not be made due to - {:?}",error)
            }
            DBErrors::DBDirectoryNotCreated { error, path } => {
                write!(f, "Directory at the desired path - {:?} could not be created kindly check permissions due to - {:?}",path.to_string_lossy().clone(),error)
            }
            DBErrors::EnvVariableNotFetched { error, var } => {
                write!(f,"DB not initialized due to environment variable {:?} could not be fetched due to - {:?}",var,error)
            }
            DBErrors::TupleAttributeParsingError { error, attribute } => {
                write!(f,"An error occurred while fetching bead from DB due to parsing of {:?} due to - {:?}",attribute,error)
            }
            DBErrors::TransactionNotRolledBack { error, query } => {
                write!(
                    f,
                    "Transaction for the query - {:?} not rolledback due to - {:?}",
                    query, error
                )
            }
            DBErrors::ConnectionToDBNotEstablished { error } => {
                write!(f, "{:?}", error)
            }
            DBErrors::InsertionTransactionNotCommitted { error, query_name } => {
                write!(
                    f,
                    "Insertion transaction of query {:?} failed due to - {:?}, therefore rolling-back the transaction",
                    query_name, error
                )
            }
            DBErrors::FetchTransactionNotCommitted { error, query_name } => {
                write!(
                    f,
                    "Fetch transaction of query {:?} failed due to- {:?}, therefore rolling-back the transaction",
                    query_name, error
                )
            }
            DBErrors::TupleNotInserted { error } => {
                write!(f, "{:?}", error)
            }
            DBErrors::TupleNotFetched { error } => {
                write!(f, "{:?}", error)
            }
        }
    }
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
        job_id: Option<u64>,
        template_id: Option<TemplateId>,
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
    InvalidShare {
        reason: String,
    },
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
    /// A bead received was not able to get persisted to DB locally
    BeadPersistenceFailed {
        error: String,
    },
    UpstreamConnectionFailed {
        error: String,
    },
    UpstreamShareForwardFailed {
        error: String,
    },
    UpstreamNotReady {
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
            StratumErrors::InvalidShare { reason } => {
                write!(f, "Invalid share: {}", reason)
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
            StratumErrors::MiningJobNotFound {
                job_id,
                template_id,
            } => {
                write!(
                    f,
                    "No mining job found with the provided job id - {:?} and template id - {:?}",
                    job_id, template_id
                )
            }
            StratumErrors::MiningJobInsertError { mining_job } => {
                write!(f,"An error occurred while inserting the following job into the mining map - {:?}",mining_job)
            }
            StratumErrors::BeadPersistenceFailed { error } => {
                write!(
                    f,
                    "Self-mined bead added to braid but not persisted to DB - {}",
                    error
                )
            }
            StratumErrors::UpstreamConnectionFailed { error } => {
                write!(f, "Failed to connect to upstream pool: {}", error)
            }
            StratumErrors::UpstreamShareForwardFailed { error } => {
                write!(f, "Failed to forward share to upstream: {}", error)
            }
            StratumErrors::UpstreamNotReady { error } => {
                write!(f, "Upstream pool is not ready: {}", error)
            }
        }
    }
}
impl std::error::Error for StratumErrors {}
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
            BraidError::MissingParent { bead, parent } => {
                write!(
                    f,
                    "Parent {} of bead {} not found in braid index",
                    parent, bead
                )
            }
            BraidError::BeadNotIndexed { bead } => {
                write!(f, "Bead {} not found in braid index", bead)
            }
            BraidError::PersistenceChannelClosed { bead } => {
                write!(
                    f,
                    "Persistence channel closed; bead {} was not persisted",
                    bead
                )
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

/// The node was asked to run against a network name that braidpool does not support.
///
/// Braidpool deliberately accepts a fixed, exact set of network names
/// (see [`crate::config::SUPPORTED_NETWORKS`]) with no aliases and no fallback:
/// silently binding to another chain would let miners produce shares that are
/// invalid for the chain the operator intended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsupportedNetworkError {
    /// The network name that was supplied by the operator.
    pub network_name: String,
}

impl fmt::Display for UnsupportedNetworkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Unsupported network {:?}, expected one of: {}",
            self.network_name,
            crate::config::SUPPORTED_NETWORKS.join(", ")
        )
    }
}
impl std::error::Error for UnsupportedNetworkError {}

/// Errors raised by the EDCA payout algorithm.
///
/// Every variant is a consensus-parameter or arithmetic fault rather than an
/// I/O failure: [`crate::payout`] is a pure function of its parameters and the
/// DAG, so these are the only ways it can fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EdcaError {
    /// The retention parameter `r = numerator / denominator` was not strictly
    /// between (0,1] .
    InvalidRetention { numerator: u64, denominator: u64 },
    /// The configured Bitcoin network difficulty `D_network` was zero.
    ZeroNetworkDifficulty,
    /// A fixed-point intermediate could not be represented.
    ArithmeticOverflow { operation: &'static str },
    /// The fee amplifier `A_i = B_base + F_i` exceeded the maximum Bitcoin
    /// amount, so the bead's committed template cannot be valid.
    FeeOverflow {
        /// The fee total, in satoshis, that could not be amplified.
        fees: u64,
    },
    /// The active UHPO state carries no weight .
    EmptyPool,
    /// A miner's payout address has no output script on the pool's network.
    UnresolvedPayoutAddress {
        /// The payout address that could not be resolved.
        payout_address: String,
    },
    /// Every nominal output fell below the network dust limit, leaving no
    /// qualifying miner to redistribute the aggregated dust to.
    NoQualifyingMiners {
        /// The dust limit in satoshis that no output reached.
        dust_limit: u64,
        /// The block reward in satoshis that was being settled.
        total_reward: u64,
    },
    /// A Q64.64 fixed-point product or sum exceeded the range of a `u128`.
    FixedPointOverflow,
    /// A weight accumulation (`U_m`, `U_total` or an output sum) overflowed.
    WeightOverflow,
    /// The fee amplifier `A_i = B_base + F_i` overflowed `u64` satoshis.
    AmplifierOverflow,
    /// A value passed where a Q64.64 fraction in `[0, 1]` was required.
    FractionOutOfRange {
        /// The offending raw Q64.64 value.
        raw: u128,
    },
    /// A bead committed a zero `weak_target`, which no hash can meet.
    ZeroBeadTarget {
        /// Index of the offending bead in `Braid::beads`.
        bead_index: usize,
    },
    /// A target ratio could not be represented as a Q64.64 fraction in `[0, 1]`.
    InvalidTargetRatio {
        /// Index of the offending bead in `Braid::beads`.
        bead_index: usize,
    },
    /// A cohort referenced a bead index that is absent from `Braid::beads`.
    BeadIndexOutOfRange {
        /// The unresolvable bead index.
        index: usize,
    },
    /// Settlement was attempted with no settleable weight, so
    /// `P_m = U_m / U_total` would divide by zero.
    EmptyState,
    /// A payout roster did not sum to the amount it was settled against, which
    /// would produce an invalid coinbase.
    RosterSumMismatch {
        /// Sum of the roster's outputs, in satoshis.
        roster_total: u64,
        /// The amount the roster was required to sum to, in satoshis.
        expected_total: u64,
    },
}

impl fmt::Display for EdcaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EdcaError::InvalidRetention {
                numerator,
                denominator,
            } => write!(
                f,
                "Invalid EDCA retention parameter {}/{}, expected 0 < r < 1",
                numerator, denominator
            ),
            EdcaError::ZeroNetworkDifficulty => {
                write!(f, "EDCA network difficulty must be non-zero")
            }
            EdcaError::ArithmeticOverflow { operation } => {
                write!(f, "EDCA fixed-point overflow while computing {}", operation)
            }
            EdcaError::FeeOverflow { fees } => write!(
                f,
                "EDCA fee amplifier overflowed for a template carrying {} satoshis in fees",
                fees
            ),
            EdcaError::EmptyPool => {
                write!(f, "EDCA active pool weight is zero, no payout is defined")
            }
            EdcaError::UnresolvedPayoutAddress { payout_address } => write!(
                f,
                "Payout address {:?} has no output script on this network",
                payout_address
            ),
            EdcaError::NoQualifyingMiners {
                dust_limit,
                total_reward,
            } => write!(
                f,
                "No EDCA payout reaches the {} satoshi dust limit when settling {} satoshis",
                dust_limit, total_reward
            ),
            EdcaError::FixedPointOverflow => {
                write!(f, "EDCA fixed-point arithmetic overflowed a u128")
            }
            EdcaError::WeightOverflow => {
                write!(f, "EDCA weight accumulation overflowed")
            }
            EdcaError::AmplifierOverflow => {
                write!(f, "EDCA fee amplifier B_base + F_i overflowed u64 satoshis")
            }
            EdcaError::FractionOutOfRange { raw } => {
                write!(f, "EDCA Q64.64 fraction {} is outside [0, 1]", raw)
            }
            EdcaError::ZeroBeadTarget { bead_index } => {
                write!(f, "Bead {} committed a zero weak_target", bead_index)
            }
            EdcaError::InvalidTargetRatio { bead_index } => write!(
                f,
                "Bead {} has a target ratio that is not representable in [0, 1]",
                bead_index
            ),
            EdcaError::BeadIndexOutOfRange { index } => {
                write!(f, "Cohort references unknown bead index {}", index)
            }
            EdcaError::EmptyState => {
                write!(f, "EDCA settlement attempted with zero total weight")
            }
            EdcaError::RosterSumMismatch {
                roster_total,
                expected_total,
            } => write!(
                f,
                "EDCA payout roster sums to {} satoshis, expected {}",
                roster_total, expected_total
            ),
        }
    }
}
impl std::error::Error for EdcaError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeeProofError {
    /// The transaction supplied as the coinbase is not a coinbase transaction.
    NotCoinbase,
    /// The bead commits to no transactions, so it has no coinbase txid.
    NoTransactions,
    /// A template's transaction fees sum past `MAX_MONEY`.
    FeeTotalOverflow,
    /// A merkle branch sibling was not 32 bytes.
    InvalidMerkleBranch {
        /// Length of the offending sibling, in bytes.
        length: usize,
    },
    /// The coinbase does not hash to the first committed txid.
    CoinbaseTxidMismatch {
        /// The first txid in the bead's `transaction_ids`.
        committed: bitcoin::Txid,
        /// The txid of the supplied coinbase.
        computed: bitcoin::Txid,
    },
    /// A txid appears more than once in the bead's `transaction_ids`.
    DuplicateTxid {
        /// The repeated txid.
        txid: bitcoin::Txid,
    },
    /// The bead builds on a different block than the state it was checked
    /// against.
    AnchorMismatch {
        /// The block the state builds on.
        expected: bitcoin::BlockHash,
        /// The block the bead's header commits to.
        found: bitcoin::BlockHash,
    },
    /// The committed txids do not produce the merkle root in the bead's header.
    MerkleRootMismatch {
        /// The merkle root in the bead's header.
        header: bitcoin::TxMerkleNode,
        /// The merkle root computed from `transaction_ids`.
        computed: bitcoin::TxMerkleNode,
    },
    /// The coinbase does not carry a valid BIP34 block height.
    InvalidBip34Height {
        /// Why the height could not be read.
        error: String,
    },
    /// The coinbase outputs sum past `MAX_MONEY`.
    CoinbaseValueOverflow,
    /// The coinbase pays out less than the block subsidy, so it implies a
    /// negative fee total.
    CoinbaseBelowSubsidy {
        /// Sum of the coinbase outputs, in satoshis.
        coinbase_value_sats: u64,
        /// The subsidy at the committed height, in satoshis.
        subsidy_sats: u64,
    },
    /// The claimed fee total differs from `coinbase value - subsidy`.
    FeeCommitmentMismatch {
        /// `fee_total_sats` from the bead's committed metadata.
        claimed_fee_sats: u64,
        /// The fee total implied by the coinbase.
        derived_fee_sats: u64,
    },
    /// Every committed transaction's fee is known, and together they pay less
    /// than the bead claims.
    FeeExceedsTransactions {
        /// The fee total the bead claims, in satoshis.
        claimed_fee_sats: u64,
        /// The fees its transactions actually pay, in satoshis.
        actual_fee_sats: u64,
    },
    /// A coinbase transaction was passed where a fee-paying transaction was
    /// required.
    CoinbaseHasNoFee,
    /// An input's spent output is unknown to this node, so the transaction's
    /// fee cannot be computed.
    MissingPrevout {
        /// The transaction being priced.
        txid: bitcoin::Txid,
        /// The outpoint whose output is unknown.
        outpoint: bitcoin::OutPoint,
    },
    /// A transaction's outputs exceed its inputs, so it could never be valid.
    NegativeFee {
        /// The offending transaction.
        txid: bitcoin::Txid,
        /// Sum of the resolved input values, in satoshis.
        input_sats: u64,
        /// Sum of the output values, in satoshis.
        output_sats: u64,
    },
    /// A transaction's values or fee left the valid money range.
    FeeOutOfRange {
        /// The offending transaction.
        txid: bitcoin::Txid,
    },
    /// Two transactions in one block spend the same output.
    DuplicateSpend {
        /// The second transaction to spend it.
        txid: bitcoin::Txid,
        /// The outpoint spent twice.
        outpoint: bitcoin::OutPoint,
    },
}

impl fmt::Display for FeeProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FeeProofError::NotCoinbase => {
                write!(f, "Supplied transaction is not a coinbase transaction")
            }
            FeeProofError::NoTransactions => {
                write!(f, "Bead commits to no transactions")
            }
            FeeProofError::FeeTotalOverflow => {
                write!(f, "Template transaction fees sum past MAX_MONEY")
            }
            FeeProofError::InvalidMerkleBranch { length } => {
                write!(f, "Merkle branch sibling is {} bytes, expected 32", length)
            }
            FeeProofError::AnchorMismatch { expected, found } => write!(
                f,
                "Bead builds on block {} but was checked against state on {}",
                found, expected
            ),
            FeeProofError::CoinbaseTxidMismatch {
                committed,
                computed,
            } => write!(
                f,
                "Coinbase txid {} does not match committed txid {}",
                computed, committed
            ),
            FeeProofError::DuplicateTxid { txid } => {
                write!(f, "Bead commits to txid {} more than once", txid)
            }
            FeeProofError::MerkleRootMismatch { header, computed } => write!(
                f,
                "Committed txids produce merkle root {}, header has {}",
                computed, header
            ),
            FeeProofError::InvalidBip34Height { error } => {
                write!(f, "Coinbase has no valid BIP34 height: {}", error)
            }
            FeeProofError::CoinbaseValueOverflow => {
                write!(f, "Coinbase outputs sum past MAX_MONEY")
            }
            FeeProofError::CoinbaseBelowSubsidy {
                coinbase_value_sats,
                subsidy_sats,
            } => write!(
                f,
                "Coinbase pays {} satoshis, below the {} satoshi subsidy",
                coinbase_value_sats, subsidy_sats
            ),
            FeeProofError::FeeCommitmentMismatch {
                claimed_fee_sats,
                derived_fee_sats,
            } => write!(
                f,
                "Bead claims {} satoshis in fees, its coinbase implies {}",
                claimed_fee_sats, derived_fee_sats
            ),
            FeeProofError::FeeExceedsTransactions {
                claimed_fee_sats,
                actual_fee_sats,
            } => write!(
                f,
                "Bead claims {} satoshis in fees, its transactions pay {}",
                claimed_fee_sats, actual_fee_sats
            ),
            FeeProofError::CoinbaseHasNoFee => {
                write!(f, "A coinbase transaction pays no fee")
            }
            FeeProofError::MissingPrevout { txid, outpoint } => write!(
                f,
                "Transaction {} spends unknown output {}, cannot compute its fee",
                txid, outpoint
            ),
            FeeProofError::NegativeFee {
                txid,
                input_sats,
                output_sats,
            } => write!(
                f,
                "Transaction {} spends {} satoshis and pays out {}",
                txid, input_sats, output_sats
            ),
            FeeProofError::FeeOutOfRange { txid } => {
                write!(f, "Transaction {} has values outside the money range", txid)
            }
            FeeProofError::DuplicateSpend { txid, outpoint } => write!(
                f,
                "Transaction {} spends output {}, already spent in the same block",
                txid, outpoint
            ),
        }
    }
}
impl std::error::Error for FeeProofError {}
