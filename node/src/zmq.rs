use crate::block_template;
use crate::shutdown::ShutdownHandler;
use futures::StreamExt;
use tokio::sync::mpsc::Sender;

pub async fn zmq_hashblock_listener(
    zmq_url: String,
    rpc: bitcoincore_rpc::Client,
    block_template_tx: Sender<bitcoincore_rpc_json::GetBlockTemplateResult>,
    shutdown_handler: ShutdownHandler,
) -> Result<(), bitcoincore_zmq::Error> {
    let mut zmq = match bitcoincore_zmq::subscribe_async(&[&zmq_url]) {
        Ok(zmq) => zmq,
        Err(e) => {
            shutdown_handler.shutdown_bitcoin_error(format!("Failed to connect to ZMQ: {}", e));
            return Err(e);
        }
    };

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
                    _ => {}
                };
            }
            Err(err) => {
                shutdown_handler.shutdown_bitcoin_error(format!("ZMQ error: {}", err));
                return Err(err);
            }
        }
    }

    Ok(())
}
