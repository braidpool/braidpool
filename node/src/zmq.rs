use crate::block_template;
use futures::StreamExt;
use tokio::sync::mpsc::Sender;

pub async fn zmq_hashblock_listener(
    zmq_url: String,
    rpc: bitcoincore_rpc::Client,
    block_template_tx: Sender<bitcoincore_rpc_json::GetBlockTemplateResult>,
) -> Result<(), bitcoincore_zmq::Error> {
    let mut zmq = bitcoincore_zmq::subscribe_single_async(&zmq_url)?;

    while let Some(msg) = zmq.next().await {
        match msg {
            Ok(m) => {
                match m {
                    bitcoincore_zmq::Message::HashBlock(_, _) => {
                        log::info!(
                            "Received a new `hashblock` notification via ZeroMQ. \
                            Calling `getblocktemplate` RPC now..."
                        );
                        block_template::fetcher(&rpc, block_template_tx.clone()).await;
                    }
                    _=> {},
                };
            }
            Err(err) => return Err(err),
        }
    }

    Ok(())
}
