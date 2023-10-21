use crate::block_template;
use tokio::sync::mpsc::{Receiver, Sender};

pub async fn setup(
    bitcoin: String,
    zmq_port: u16,
) -> Result<
    Receiver<Result<bitcoincore_zmq::Message, bitcoincore_zmq::Error>>,
    bitcoincore_zmq::Error,
> {
    let zmq_url = format!("tcp://{}:{}", bitcoin, zmq_port);

    bitcoincore_zmq::subscribe_single(&zmq_url).await
}

pub async fn listener(
    mut zmq: Receiver<Result<bitcoincore_zmq::Message, bitcoincore_zmq::Error>>,
    rpc: bitcoincore_rpc::Client,
    block_template_tx: Sender<bitcoincore_rpc_json::GetBlockTemplateResult>,
) -> Result<(), bitcoincore_zmq::Error> {
    while let Some(msg) = zmq.recv().await {
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
                    bitcoincore_zmq::Message::HashTx(_, _) => todo!(),
                    bitcoincore_zmq::Message::Block(_, _) => todo!(),
                    bitcoincore_zmq::Message::Tx(_, _) => todo!(),
                    bitcoincore_zmq::Message::Sequence(_, _) => todo!(),
                };
            }
            Err(err) => return Err(err),
        }
    }

    Ok(())
}
