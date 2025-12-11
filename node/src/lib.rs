//These implementations must be defined under lib.rs as they are required for intergration tests
use bitcoin::consensus::encode::deserialize;
use std::{collections::HashMap, sync::Arc};

use futures::lock::Mutex;
use tokio::sync::mpsc::{self, Receiver, Sender};
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

/// Maximum number of block templates to retain in the in-memory cache.
///
/// This constant limits how many recent block templates, fetched via IPC from Bitcoin node,
/// are kept available for downstream miners. When the cache exceeds this size, the oldest
/// templates are evicted to make room for new ones. This helps prevent unbounded memory
/// growth and ensures efficient resource usage.
pub const MAX_CACHED_TEMPLATES: usize = 90;

use crate::{
    db::BraidpoolDBTypes,
    error::IPCtemplateError,
    stratum::{BlockTemplate, NotifyCmd},
};
use std::error::Error;
#[macro_use]
pub mod macros;
pub mod bead;
pub mod behaviour;
pub mod braid;
pub mod cli;
pub mod committed_metadata;
pub mod config;
pub mod db;
pub mod error;
pub mod ibd_manager;
pub mod ipc;
pub mod peer_manager;
pub mod rpc_server;
pub mod stratum;
pub mod template_creator;
pub mod uncommitted_metadata;
pub mod utils;
use std::sync::atomic::{AtomicU64, Ordering};

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

/// Unique identifier assigned to each block template.
pub type TemplateId = u64;

/// Global template ID counter that persists across the application lifetime
static GLOBAL_TEMPLATE_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Get the next unique template ID (increments on each call)
pub fn get_next_template_id() -> TemplateId {
    GLOBAL_TEMPLATE_COUNTER.fetch_add(1, Ordering::SeqCst)
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
    mut template_rx: mpsc::Receiver<Arc<crate::ipc::client::BlockTemplate>>,
    notifier_tx: mpsc::Sender<NotifyCmd>,
    latest_template_arc: &mut Arc<Mutex<BlockTemplate>>,
    latest_template_merkle_branch_arc: &mut Arc<Mutex<Vec<Vec<u8>>>>,
    template_cache: Arc<
        tokio::sync::Mutex<HashMap<TemplateId, Arc<crate::ipc::client::BlockTemplate>>>,
    >,
    latest_template_id: Arc<Mutex<TemplateId>>,
) -> Result<(), IPCtemplateError> {
    while let Some(ipc_template) = template_rx.recv().await {
        let template_bytes = match &ipc_template.processed_block_hex {
            Some(processed_hex) if !processed_hex.is_empty() => processed_hex,
            _ => {
                warn!(
                    field = "processed_block_hex",
                    "Skipping invalid template - hex payload missing"
                );
                continue;
            }
        };

        if template_bytes.len() > 0 {
            // Generate new template_id for every template
            let template_id = get_next_template_id();
            {
                let mut latest_id = latest_template_id.lock().await;
                *latest_id = template_id;
            }

            // Cache the IPC template with this new ID
            {
                let mut cache = template_cache.lock().await;
                cache.insert(template_id, ipc_template.clone());

                // Cleanup old templates
                if cache.len() > MAX_CACHED_TEMPLATES {
                    let mut ids: Vec<TemplateId> = cache.keys().copied().collect();
                    ids.sort_unstable();

                    let remove_count = cache.len() - MAX_CACHED_TEMPLATES;
                    for id in ids.iter().take(remove_count) {
                        cache.remove(id);
                        debug!(template_id = %id, "Removed old template from cache");
                    }
                }
            }

            let candidate_block: Result<
                bitcoin::blockdata::block::Block,
                bitcoin::consensus::DeserializeError,
            > = deserialize(&template_bytes);

            let merkle_branch_coinbase = ipc_template.components.coinbase_merkle_path.clone();
            let (template_header, template_transactions) = candidate_block.unwrap().into_parts();
            let _coinbase_transaction = template_transactions.get(0);

            debug!(template_id = %template_id, template_header = ?template_header, "New block template");
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
            for branch in merkle_branch_coinbase.iter() {
                latest_template_merkle_branch.push(branch.clone());
            }
            info!(
                template_id = %template_id,
                tx_count = %template_transactions.len(),
                "New block template"
            );

            let notification_sent_or_not = notifier_tx
                .send(NotifyCmd::SendToAll {
                    template: template,
                    merkle_branch_coinbase,
                    template_id,
                })
                .await;
            match notification_sent_or_not {
                Ok(_) => {
                    debug!(template_id = %template_id, "Template sent to notifier");
                }
                Err(error) => {
                    error!(error = ?error, "Failed to send template notification");
                }
            }
        } else {
            warn!(size_bytes = 0, expected_min = 80, "IPC template too short");
        }
    }

    Ok(())
}
pub enum SwarmCommand {
    //Initiate IBD after waiting for connection_mapping to be populated via peer discovery
    InitiateIBD,
    PropagateMinedBead {
        candidate_block: bitcoin::Block,
        extranonce_2_raw_value: u32,
        downstream_client_ip: String,
        job_sent_timestamp: u32,
        downstream_payout_addr: String,
        //TODO: Will be used as seperate entity after altering `uncommitted_metadata`
        extranonce_1_raw_value: u32,
    },
}
pub struct SwarmHandler {
    pub command_sender: Sender<SwarmCommand>,
    db_command_sender: tokio::sync::mpsc::Sender<BraidpoolDBTypes>,
}
impl SwarmHandler {
    pub fn new(
        db_command_sender: tokio::sync::mpsc::Sender<BraidpoolDBTypes>,
    ) -> (Self, Receiver<SwarmCommand>) {
        let (swarm_stratum_bridge_tx, swarm_stratum_bridge_rx) =
            mpsc::channel::<SwarmCommand>(1024);
        (
            Self {
                command_sender: swarm_stratum_bridge_tx,
                db_command_sender,
            },
            swarm_stratum_bridge_rx,
        )
    }
}

pub fn setup_tracing() -> Result<(), Box<dyn Error>> {
    // Create a filter that uses RUST_LOG environment variable if set,
    // otherwise falls back to reasonable defaults
    let filter = if std::env::var("RUST_LOG").is_ok() {
        // If RUST_LOG is set, use it exactly as provided
        tracing_subscriber::EnvFilter::from_default_env()
    } else {
        // If no RUST_LOG is set, use sensible defaults
        tracing_subscriber::EnvFilter::from_default_env()
            .add_directive("node=info".parse()?)
            .add_directive("libp2p=info".parse()?)
    };

    // Enable file and line number logging when RUST_LOG includes debug or trace
    let show_location = std::env::var("RUST_LOG")
        .map(|v| v.contains("debug") || v.contains("trace"))
        .unwrap_or(false);

    // Build and initialize a `tracing` subscriber with the specified filter, colors, and target/module prefixes
    // The .init() method automatically calls LogTracer::init() when the tracing-log feature is enabled,
    // which intercepts log:: calls from dependencies (like libp2p, sqlx) and forwards them to tracing
    tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .with_target(true) // Show the target/module (e.g., "libp2p::kad", "node::main")
        .with_thread_ids(false) // Set to true if you want thread IDs
        .with_thread_names(false) // Set to true if you want thread names
        .with_file(show_location) // Show file names when RUST_LOG=debug or RUST_LOG=trace
        .with_line_number(show_location) // Show line numbers when RUST_LOG=debug or RUST_LOG=trace
        .with_ansi(true) // Enable ANSI colors
        .compact() // Use a more compact format that works well with colors
        .init();

    Ok(())
}
