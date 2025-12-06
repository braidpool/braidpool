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
// Maximum backoff in seconds (about 18 hours) - prevents overflow
const MAX_BACKOFF_SECS: u64 = 65536;

pub async fn fetcher(
    rpc: &bitcoincore_rpc::Client,
    block_template_tx: Sender<GetBlockTemplateResult>,
) {
    let mut rpc_failure_counter = 0;
    let mut rpc_failure_backoff;

    loop {
        match rpc.get_block_template(GetBlockTemplateModes::Template, &BLOCK_TEMPLATE_RULES, &[]) {
            Ok(get_block_template_result) => {
                if let Err(e) = block_template_tx
                    .send(get_block_template_result.clone())
                    .await
                {
                    log::error!(
                        "Failed to send block template over mpsc channel: {}. \
                        Receiver may have been dropped.",
                        e
                    );
                }
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
                // Use saturating_pow to prevent overflow, then cap at MAX_BACKOFF_SECS
                rpc_failure_backoff = BACKOFF_BASE
                    .saturating_pow(rpc_failure_counter)
                    .min(MAX_BACKOFF_SECS);

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
