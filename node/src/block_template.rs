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

#[derive(Debug)]
pub enum BlockTemplateError {
    Rpc(bitcoincore_rpc::Error),
    Zmq(bitcoincore_zmq::Error),
}

async fn zmq_setup(
    bitcoin: String,
    zmq_port: u16,
) -> Result<Receiver<Result<bitcoincore_zmq::Message, bitcoincore_zmq::Error>>, BlockTemplateError>
{
    let zmq_url = format!("tcp://{}:{}", bitcoin, zmq_port);

    match bitcoincore_zmq::subscribe_single(&zmq_url).await {
        Ok(zmq) => Ok(zmq),
        Err(err) => Err(BlockTemplateError::Zmq(err)),
    }
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
    let mut zmq: Receiver<Result<bitcoincore_zmq::Message, bitcoincore_zmq::Error>> =
        zmq_setup(bitcoin, zmq_port).await?;

    while let Some(msg) = zmq.recv().await {
        match msg {
            Ok(m) => {
                match m {
                    bitcoincore_zmq::Message::HashBlock(_, _) => {
                        log::info!(
                            "Received a new `hashblock` notification via ZeroMQ. \
                            Calling `getblocktemplate` RPC now..."
                        );
                        fetcher(&rpc, block_template_tx.clone()).await;
                    }
                    bitcoincore_zmq::Message::HashTx(_, _) => todo!(),
                    bitcoincore_zmq::Message::Block(_, _) => todo!(),
                    bitcoincore_zmq::Message::Tx(_, _) => todo!(),
                    bitcoincore_zmq::Message::Sequence(_, _) => todo!(),
                };
            }
            Err(err) => return Err(BlockTemplateError::Zmq(err)),
        }
    }

    Ok(())
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
