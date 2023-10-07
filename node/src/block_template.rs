use bitcoincore_rpc::{Auth, Client, RpcApi};
use bitcoincore_rpc_json::{GetBlockTemplateModes, GetBlockTemplateResult, GetBlockTemplateRules};
use std::error::Error;
use tokio::sync::mpsc::{Receiver, Sender};
use tokio::time::{sleep, Duration};
use chrono::prelude::*;

const BLOCK_TEMPLATE_RULES: [GetBlockTemplateRules; 4] = [
    GetBlockTemplateRules::SegWit,
    GetBlockTemplateRules::Signet,
    GetBlockTemplateRules::Csv,
    GetBlockTemplateRules::Taproot,
];

pub async fn poll(
    rpc_url: String,
    rpc_user: String,
    rpc_pass: String,
    poll_interval: u64,
    block_template_tx: Sender<GetBlockTemplateResult>,
) -> Result<(), Box<dyn Error + Send>> {
    let rpc = Client::new(&rpc_url, Auth::UserPass(rpc_user, rpc_pass)).unwrap();
    
    let mut last_block_template = rpc
        .get_block_template(GetBlockTemplateModes::Template, &BLOCK_TEMPLATE_RULES, &[])
        .unwrap();
    block_template_tx.send(last_block_template.clone()).await.unwrap();

    loop {
        // sleep until it's time to poll again
        sleep(Duration::from_secs(poll_interval.clone())).await;

        let block_template = rpc
            .get_block_template(GetBlockTemplateModes::Template, &BLOCK_TEMPLATE_RULES, &[])
            .unwrap();

        // check if this is a new template
        if block_template.previous_block_hash != last_block_template.previous_block_hash {
            block_template_tx.send(block_template.clone()).await.unwrap();
        }

        last_block_template = block_template;
    }
}

// dummy placeholder function to consume the newly found block templates
pub async fn consumer(mut block_template_rx: Receiver<GetBlockTemplateResult>) {
    while let Some(block_template) = block_template_rx.recv().await {
        let now = Local::now();
        println!("[{:0>2}:{:0>2}:{:0>2}] Received new block template: {:?}", now.hour(), now.minute(), now.second(), block_template);
    }
}
