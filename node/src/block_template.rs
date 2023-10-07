use bitcoincore_rpc::{bitcoin, bitcoin::hashes::Hash, Auth, Client, RpcApi};
use bitcoincore_rpc_json::{GetBlockTemplateModes, GetBlockTemplateResult, GetBlockTemplateRules};
use chrono::prelude::*;
use std::error::Error;
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

pub async fn poll(
    rpc_url: String,
    rpc_user: String,
    rpc_pass: String,
    poll_interval: u64,
    block_template_tx: Sender<GetBlockTemplateResult>,
) -> Result<(), Box<dyn Error + Send>> {
    let mut rpc_failure_counter = 0;
    let mut rpc_failure_backoff;
    let mut last_block_template_parent_hash = bitcoin::BlockHash::all_zeros();

    let rpc = Client::new(&rpc_url, Auth::UserPass(rpc_user, rpc_pass)).unwrap();

    loop {
        match rpc.get_block_template(GetBlockTemplateModes::Template, &BLOCK_TEMPLATE_RULES, &[]) {
            Ok(get_block_template_result) => {
                if get_block_template_result.previous_block_hash != last_block_template_parent_hash
                {
                    // send block template over mpsc channel
                    block_template_tx
                        .send(get_block_template_result.clone())
                        .await
                        .unwrap();

                    // prepare for next loop
                    last_block_template_parent_hash = get_block_template_result.previous_block_hash;
                    rpc_failure_counter = 0;

                    // sleep until it's time to poll again
                    sleep(Duration::from_secs(poll_interval.clone())).await;
                }
            }
            Err(_) => {
                rpc_failure_counter += 1;
                if rpc_failure_counter > MAX_RPC_FAILURES {
                    println!("Exceeded the maximum number of failed getblocktemplate RPC attempts. Halting.");
                    std::process::exit(1);
                }
                rpc_failure_backoff = u64::checked_pow(BACKOFF_BASE, rpc_failure_counter.clone())
                    .expect("MAX_RPC_FAILURES doesn't allow overflow; qed");

                // sleep until it's time to poll again
                sleep(Duration::from_secs(rpc_failure_backoff)).await;
            }
        };
    }
}

// dummy placeholder function to consume the newly found block templates
pub async fn consumer(mut block_template_rx: Receiver<GetBlockTemplateResult>) {
    while let Some(block_template) = block_template_rx.recv().await {
        let now = Local::now();
        println!(
            "[{:0>2}:{:0>2}:{:0>2}] Received new block template: {:?}",
            now.hour(),
            now.minute(),
            now.second(),
            block_template
        );
    }
}
