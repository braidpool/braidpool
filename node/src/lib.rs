use bitcoin::consensus::encode::deserialize;
use std::sync::Arc;

use futures::lock::Mutex;
use tokio::sync::mpsc;

use crate::{
    error::IPCtemplateError,
    stratum::{BlockTemplate, NotifyCmd},
};
use std::error::Error;
pub mod bead;
pub mod behaviour;
pub mod block_template;
pub mod braid;
pub mod cli;
pub mod committed_metadata;
pub mod common_capnp;
pub mod config;
pub mod echo_capnp;
pub mod error;
pub mod init_capnp;
pub mod ipc;
pub mod mining_capnp;
pub mod peer_manager;
pub mod proxy_capnp;
pub mod rpc;
pub mod rpc_server;
pub mod stratum;
pub mod template_creator;
pub mod uncommitted_metadata;
pub mod utils;
pub mod zmq;

pub async fn ipc_template_consumer(
    mut template_rx: mpsc::Receiver<(Vec<u8>, Vec<Vec<u8>>)>,
    notifier_tx: mpsc::Sender<NotifyCmd>,
    latest_template_arc: &mut Arc<Mutex<BlockTemplate>>,
    latest_template_merkel_branch_arc: &mut Arc<Mutex<Vec<Vec<u8>>>>,
) -> Result<(), IPCtemplateError> {
    while let Some(template_bytes) = template_rx.recv().await {
        if template_bytes.0.len() > 0 {
            let candidate_block: Result<
                bitcoin::blockdata::block::Block,
                bitcoin::consensus::DeserializeError,
            > = deserialize(&template_bytes.0.clone());
            let merkel_branch_coinbase = template_bytes.1.clone();
            let (template_header, template_transactions) = candidate_block.unwrap().into_parts();
            let coinbase_transaction = template_transactions.get(0);
            log::info!("Coinbase transaction is - {:?}", coinbase_transaction);
            log::info!(
                "The block header for the given template is - {:?}",
                template_header
            );
            log::info!("Transactions count is - {}", template_transactions.len());
            let template: BlockTemplate = BlockTemplate::default();
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
            latest_template.bits = template.bits.clone();
            latest_template.height = template.height;
            latest_template.default_witness_commitment =
                template.default_witness_commitment.clone();
            let mut latest_template_merkel_branch = latest_template_merkel_branch_arc.lock().await;
            latest_template_merkel_branch.clear();
            for branch in template_bytes.1.into_iter() {
                latest_template_merkel_branch.push(branch);
            }
            log::info!(
                "Latest template has been updated with the most recently received template from IPC"
            );

            let notification_sent_or_not = notifier_tx
                .send(NotifyCmd::SendToAll {
                    template: template,
                    merkel_branch_coinbase,
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
