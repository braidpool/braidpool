//These implementations must be defined under lib.rs as they are required for intergration tests
use bitcoin::{
    consensus::encode::deserialize, ecdsa::Signature, BlockHash, CompactTarget, EcdsaSighashType,
};
use num::ToPrimitive;
use std::{collections::HashSet, str::FromStr, sync::Arc, time::UNIX_EPOCH};

use futures::lock::Mutex;
use tokio::sync::mpsc::{self, Receiver, Sender};

use crate::{
    bead::Bead,
    committed_metadata::{CommittedMetadata, TimeVec},
    error::{IPCtemplateError, StratumErrors},
    stratum::{BlockTemplate, NotifyCmd},
    uncommitted_metadata::UnCommittedMetadata,
};
use std::error::Error;
pub mod bead;
pub mod behaviour;
pub mod braid;
pub mod cli;
pub mod committed_metadata;
pub mod config;
pub mod error;
pub mod ipc;
pub mod peer_manager;
pub mod rpc_server;
pub mod stratum;
pub mod template_creator;
pub mod uncommitted_metadata;
pub mod utils;
//Including the capnp modules after building while compiling the workspace.package
pub mod proxy_capnp {
    include!(concat!(env!("OUT_DIR"), "/proxy_capnp.rs"));
}
pub mod mining_capnp {
    include!(concat!(env!("OUT_DIR"), "/mining_capnp.rs"));
}
pub mod echo_capnp {
    include!(concat!(env!("OUT_DIR"), "/echo_capnp.rs"));
}
pub mod common_capnp {
    include!(concat!(env!("OUT_DIR"), "/common_capnp.rs"));
}
pub mod init_capnp {
    include!(concat!(env!("OUT_DIR"), "/init_capnp.rs"));
}

/// **Length of the extranonce prefix (in bytes).**
///
/// In Stratum mining, the extranonce is split into two parts:
/// `EXTRANONCE1` (prefix) and `EXTRANONCE2` (suffix).
///
/// This constant defines the size of `EXTRANONCE1` as **4 bytes**.
/// Typically assigned by the mining pool to uniquely identify a miner generated randomly or can be done via the peer_addr hash.
pub const EXTRANONCE1_SIZE: usize = 4;

/// **Length of the extranonce suffix (in bytes).**
///
///These are the rollable bits defined under the extanonce,along with nonce and Version which can be worked upon to produce suitable valid share
/// being submitted by the miner via `mining.submit` .
pub const EXTRANONCE2_SIZE: usize = 4;
/// **Separator between `EXTRANONCE1` and `EXTRANONCE2`.**
///
/// This is an array of bytes used to clearly delimit the two extranonce parts.
/// In this testing configuration, the separator length equals
/// `EXTRANONCE1_SIZE + EXTRANONCE2_SIZE` (8 bytes total),
/// and is filled with the byte value `1u8` for simplicity.
/// can be changed accordingly as per discussion .
pub const EXTRANONCE_SEPARATOR: [u8; EXTRANONCE1_SIZE + EXTRANONCE2_SIZE] =
    [1u8; EXTRANONCE1_SIZE + EXTRANONCE2_SIZE];
/// Consumes block templates received via an IPC channel, updates shared state,
/// and notifies all connected consumers.
///
/// # Parameters
///
/// * `template_rx` - An asynchronous mpsc receiver providing block templates.
///   Each message is a tuple:
///     - `Vec<u8>`: Raw serialized block data.
///     - `Vec<Vec<u8>>`: Merkle branch data for the coinbase transaction.
/// * `notifier_tx` - An asynchronous mpsc sender used to notify all connected
///   components when a new block template is available.
/// * `latest_template_arc` - A thread-safe, mutable reference to the shared
///   [`BlockTemplate`] state, wrapped in an [`Arc`] and [`Mutex`].
/// * `latest_template_merkle_branch_arc` - A thread-safe, mutable reference to the
///   latest Merkle branch data for the coinbase transaction, wrapped in an [`Arc`] and [`Mutex`].
///
/// # Returns
///
/// * `Ok(())` - When the consumer loop completes without errors.
/// * `Err(IPCtemplateError)` - If an unrecoverable IPC template handling error occurs.
pub async fn ipc_template_consumer(
    mut template_rx: mpsc::Receiver<(Vec<u8>, Vec<Vec<u8>>)>,
    notifier_tx: mpsc::Sender<NotifyCmd>,
    latest_template_arc: &mut Arc<Mutex<BlockTemplate>>,
    latest_template_merkle_branch_arc: &mut Arc<Mutex<Vec<Vec<u8>>>>,
) -> Result<(), IPCtemplateError> {
    while let Some(template_bytes) = template_rx.recv().await {
        if template_bytes.0.len() > 0 {
            let candidate_block: Result<
                bitcoin::blockdata::block::Block,
                bitcoin::consensus::DeserializeError,
            > = deserialize(&template_bytes.0.clone());
            let merkle_branch_coinbase = template_bytes.1.clone();
            let (template_header, template_transactions) = candidate_block.unwrap().into_parts();
            let coinbase_transaction = template_transactions.get(0);
            log::info!("Coinbase transaction is - {:?}", coinbase_transaction);
            log::info!(
                "The block header for the given template is - {:?}",
                template_header
            );
            log::info!("Transactions count is - {}", template_transactions.len());
            let template: BlockTemplate = BlockTemplate {
                version: template_header.version,
                previousblockhash: template_header.prev_blockhash,
                transactions: template_transactions.clone(),
                curtime: template_header.time,
                bits: template_header.bits,
                ..Default::default()
            };

            let mut latest_template = latest_template_arc.lock().await;
            latest_template.version = template.version;
            latest_template.rules = template.rules.clone();
            latest_template.vbavailable = template.vbavailable.clone();
            latest_template.vbrequired = template.vbrequired;
            latest_template.previousblockhash = template.previousblockhash.clone();
            latest_template.transactions = template.transactions.clone();
            latest_template.coinbaseaux = template.coinbaseaux.clone();
            latest_template.coinbasevalue = template.coinbasevalue;
            latest_template.longpollid = template.longpollid.clone();
            latest_template.target = template.target.clone();
            latest_template.mintime = template.mintime;
            latest_template.mutable = template.mutable.clone();
            latest_template.noncerange = template.noncerange.clone();
            latest_template.sigoplimit = template.sigoplimit;
            latest_template.sizelimit = template.sizelimit;
            latest_template.weightlimit = template.weightlimit;
            latest_template.curtime = template.curtime;
            latest_template.bits = template.bits;
            latest_template.height = template.height;
            latest_template.default_witness_commitment =
                template.default_witness_commitment.clone();
            let mut latest_template_merkle_branch = latest_template_merkle_branch_arc.lock().await;
            latest_template_merkle_branch.clear();
            for branch in template_bytes.1.into_iter() {
                latest_template_merkle_branch.push(branch);
            }
            log::info!(
                "Latest template has been updated with the most recently received template from IPC"
            );

            let notification_sent_or_not = notifier_tx
                .send(NotifyCmd::SendToAll {
                    template: template,
                    merkle_branch_coinbase,
                })
                .await;
            match notification_sent_or_not {
                Ok(_) => {
                    log::info!("Template has been sent to the notifier");
                }
                Err(error) => {
                    log::error!("An error occurred while sending notification - {:?}", error);
                }
            }
        } else {
            log::warn!("IPC template too short: 0 bytes");
        }
    }

    Ok(())
}
pub enum SwarmCommand {
    PropagateValidBead { bead_bytes: Vec<u8> },
}
pub struct SwarmHandler {
    pub command_sender: Sender<SwarmCommand>,
}
impl SwarmHandler {
    pub fn new() -> (Self, Receiver<SwarmCommand>) {
        let (swarm_stratum_bridge_tx, swarm_stratum_bridge_rx) =
            mpsc::channel::<SwarmCommand>(1024);
        (
            Self {
                command_sender: swarm_stratum_bridge_tx,
            },
            swarm_stratum_bridge_rx,
        )
    }
    pub async fn propagate_valid_bead(
        &mut self,
        candidate_block: bitcoin::Block,
        extranonce_2_raw_value: i32,
        downstream_client_ip: &str,
        job_sent_timestamp: u32,
        downstream_payout_addr: &str,
    ) -> Result<(), StratumErrors> {
        let (candidate_block_header, candidate_block_transactions) = candidate_block.into_parts();
        log::info!("Received command for broadcasting bead via floodsub");
        //TODO:Currently temprorary placeholder will be replaced in upcoming PRs
        let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
            .parse::<bitcoin::PublicKey>()
            .unwrap();
        let time_hash_set = TimeVec(Vec::new());
        let parent_hash_set: HashSet<BlockHash> = HashSet::new();
        //TODO:This will be replaced via the allotted `WeakShareDifficulty` after Difficulty adjustment
        let weak_target = CompactTarget::from_consensus(32);
        //Mindiff
        let min_target = CompactTarget::from_consensus(1);
        //Job sent time before downstream starts mining
        let job_notification_time_val =
            bitcoin::blockdata::locktime::absolute::Time::from_consensus(job_sent_timestamp)
                .unwrap();
        let candidate_block_bead_committed_metadata = CommittedMetadata {
            comm_pub_key: public_key,
            transactions: candidate_block_transactions,
            parents: parent_hash_set,
            parent_bead_timestamps: time_hash_set,
            payout_address: downstream_payout_addr.to_string(),
            start_timestamp: job_notification_time_val,
            min_target: min_target,
            weak_target: weak_target,
            miner_ip: downstream_client_ip.to_string(),
        };
        //TODO:This will be either be generated via the `Pubkey` from config parameter from `~/.braidpool`
        let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
        let sig = Signature {
            signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
            sighash_type: EcdsaSighashType::All,
        };
        //Current UNIX timestamp during broadcast of bead
        let current_system_time = std::time::SystemTime::now();
        let duration_since_epoch = match current_system_time.duration_since(UNIX_EPOCH) {
            Ok(duration) => duration,
            Err(error) => {
                return Err(StratumErrors::ErrorFetchingCurrentUNIXTimestamp {
                    error: error.to_string(),
                })
            }
        };

        let unix_timestamp = duration_since_epoch.as_secs().to_u32().unwrap();

        let candidate_block_bead_uncommitted_metadata = UnCommittedMetadata {
            broadcast_timestamp: bitcoin::blockdata::locktime::absolute::MedianTimePast::from_u32(
                unix_timestamp,
            )
            .unwrap(),
            extra_nonce: extranonce_2_raw_value,
            signature: sig,
        };
        let weak_share = Bead {
            committed_metadata: candidate_block_bead_committed_metadata,
            block_header: candidate_block_header,
            uncommitted_metadata: candidate_block_bead_uncommitted_metadata,
        };
        let serialized_weak_share_bytes = bitcoin::consensus::serialize(&weak_share);
        //After validation of the candidate block constructed by the downstream node sending it to swarm for further propogation
        match self
            .command_sender
            .send(SwarmCommand::PropagateValidBead {
                bead_bytes: serialized_weak_share_bytes,
            })
            .await
        {
            Ok(_) => {
                log::info!("Candidate block sent to swarm after PoW validation");
            }
            Err(error) => {
                log::error!(
                    "An error occurred while sending candidate block to swarm after PoW validation"
                );
                return Err(StratumErrors::CandidateBlockNotSent {
                    error: error.to_string(),
                });
            }
        };
        Ok(())
    }
}
///Initializing the logger via `tokio_trace`
pub fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

pub fn setup_tracing() -> Result<(), Box<dyn Error>> {
    // Create a filter for controlling the verbosity of tracing output
    let filter =
        tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);

    // Build a `tracing` subscriber with the specified filter
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    // Set the subscriber as the global default for tracing
    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber failed");

    Ok(())
}
