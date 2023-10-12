use bitcoincore_rpc::RpcApi;
use bitcoincore_rpc_json::{GetBlockTemplateModes, GetBlockTemplateResult, GetBlockTemplateRules};
use chrono::prelude::*;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc::{Receiver, Sender};
use tokio::time::{sleep, Duration};

const BLOCK_TEMPLATE_RULES: [GetBlockTemplateRules; 4] = [
    GetBlockTemplateRules::SegWit,
    GetBlockTemplateRules::Signet,
    GetBlockTemplateRules::Csv,
    GetBlockTemplateRules::Taproot,
];

const BACKOFF_BASE: u64 = 2;
const MAX_RPC_FAILURES: u32 = 20;

#[derive(Debug)]
pub enum BlockTemplateError {
    Rpc(bitcoincore_rpc::Error),
    Zmq(zmq::Error),
}

fn zmq_setup(
    bitcoin: String,
    zmq_port: u16,
) -> Result<Arc<Mutex<zmq::Socket>>, BlockTemplateError> {
    let zmq_url = format!("tcp://{}:{}", bitcoin, zmq_port);
    let zmq_ctx = zmq::Context::new();

    let zmq_socket = match zmq_ctx.socket(zmq::SUB) {
        Ok(socket) => socket,
        Err(err) => return Err(BlockTemplateError::Zmq(err)),
    };

    if let Err(err) = zmq_socket.connect(&zmq_url) {
        return Err(BlockTemplateError::Zmq(err));
    }

    if let Err(err) = zmq_socket.set_subscribe(b"hashblock") {
        return Err(BlockTemplateError::Zmq(err));
    }

    Ok(Arc::new(Mutex::new(zmq_socket)))
}

fn rpc_setup(
    bitcoin: String,
    rpc_port: u16,
    rpc_user: String,
    rpc_pass: String,
) -> Result<bitcoincore_rpc::Client, BlockTemplateError> {
    let rpc_url = format!("{}:{}", bitcoin, rpc_port);
    match bitcoincore_rpc::Client::new(
        &rpc_url,
        bitcoincore_rpc::Auth::UserPass(rpc_user, rpc_pass),
    ) {
        Ok(client) => Ok(client),
        Err(err) => Err(BlockTemplateError::Rpc(err)),
    }
}

pub async fn listener(
    bitcoin: String,
    rpc_port: u16,
    rpc_user: String,
    rpc_pass: String,
    zmq_port: u16,
    block_template_tx: Sender<GetBlockTemplateResult>,
) -> Result<(), BlockTemplateError> {
    let rpc: bitcoincore_rpc::Client = rpc_setup(bitcoin.clone(), rpc_port, rpc_user, rpc_pass)?;
    let zmq: Arc<Mutex<zmq::Socket>> = zmq_setup(bitcoin, zmq_port)?;

    loop {
        let zmq_clone = Arc::clone(&zmq);

        match tokio::task::spawn_blocking(move || {
            let zmq = zmq_clone.lock().expect("lock zmq socket");
            zmq.recv_multipart(0)
        })
        .await
        .expect("receive zmq notification")
        {
            // This is simply a trigger to call the `getblocktemplate` RPC via `fetcher`.
            // As long as we only subscribe to the `hashblock` topic, we don't really need to
            // deserialize the multipart message.
            Ok(_msg) => {
                println!(
                    "{} Received a new `hashblock` notification via ZeroMQ. \
                    Calling `getblocktemplate` RPC now...",
                    format_now()
                );
                fetcher(&rpc, block_template_tx.clone()).await;
            }
            Err(err) => return Err(BlockTemplateError::Zmq(err)),
        };
    }
}

pub async fn fetcher(
    rpc: &bitcoincore_rpc::Client,
    block_template_tx: Sender<GetBlockTemplateResult>,
) {
    let mut rpc_failure_counter = 0;
    let mut rpc_failure_backoff;

    loop {
        match rpc.get_block_template(GetBlockTemplateModes::Template, &BLOCK_TEMPLATE_RULES, &[]) {
            Ok(get_block_template_result) => {
                block_template_tx
                    .send(get_block_template_result.clone())
                    .await
                    .expect("send block template over mpsc channel");
                break;
            }
            Err(e) => {
                rpc_failure_counter += 1;
                if rpc_failure_counter > MAX_RPC_FAILURES {
                    println!("Exceeded the maximum number of failed `getblocktemplate` RPC attempts. Halting.");
                    std::process::exit(1);
                }
                rpc_failure_backoff = u64::checked_pow(BACKOFF_BASE, rpc_failure_counter.clone())
                    .expect("MAX_RPC_FAILURES doesn't allow overflow; qed");

                // sleep until it's time to try again
                println!("{}, Error on `getblocktemplate` RPC: {}", format_now(), e);
                println!(
                    "Exponential Backoff: `getblocktemplate` RPC failed {} times, waiting {} \
                    seconds before attempting `getblocktemplate` RPC again.",
                    rpc_failure_counter, rpc_failure_backoff
                );
                sleep(Duration::from_secs(rpc_failure_backoff)).await;
            }
        }
    }
}

// dummy placeholder function to consume the received block templates
pub async fn consumer(mut block_template_rx: Receiver<GetBlockTemplateResult>) {
    let mut last_block_template_height = 0;
    while let Some(block_template) = block_template_rx.recv().await {
        // if block template is from some outdated exponential backoff RPC, ignore it
        if block_template.height > last_block_template_height {
            println!(
                "{} Received new block template via `getblocktemplate` RPC: {:?}",
                format_now(),
                block_template
            );
            last_block_template_height = block_template.height;
        }
    }
}

fn format_now() -> String {
    let now = Local::now();
    format!(
        "[{:0>2}:{:0>2}:{:0>2}]",
        now.hour(),
        now.minute(),
        now.second(),
    )
}
