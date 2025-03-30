use bitcoincore_rpc::RpcApi;
use bitcoincore_rpc_json::{GetBlockTemplateModes, GetBlockTemplateResult, GetBlockTemplateRules};
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
                    log::error!(
                        "Exceeded the maximum number of failed `getblocktemplate` RPC \
                    attempts. Halting."
                    );
                    std::process::exit(1);
                }
                rpc_failure_backoff = u64::checked_pow(BACKOFF_BASE, rpc_failure_counter.clone())
                    .expect("MAX_RPC_FAILURES doesn't allow overflow; qed");

                // sleep until it's time to try again
                log::error!("Error on `getblocktemplate` RPC: {}", e);
                log::error!(
                    "Exponential Backoff: `getblocktemplate` RPC failed {} times, waiting {} \
                    seconds before attempting `getblocktemplate` RPC again.",
                    rpc_failure_counter,
                    rpc_failure_backoff
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
            log::info!(
                "Received new block template via `getblocktemplate` RPC: {:?}",
                block_template
            );
            last_block_template_height = block_template.height;
        }
    }
}
