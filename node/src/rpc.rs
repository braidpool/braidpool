use bitcoincore_rpc::RpcApi;
use shellexpand;
use std::path::PathBuf;
use crate::shutdown::ShutdownHandler;

pub fn setup(
    bitcoin: String,
    rpc_port: u16,
    rpc_user: Option<String>,
    rpc_pass: Option<String>,
    rpc_cookie: Option<String>,
) -> Result<bitcoincore_rpc::Client, bitcoincore_rpc::Error> {
    let rpc_url = format!("{}:{}", bitcoin, rpc_port);
    let (rpc, is_cookie_auth) = if rpc_user.is_some() {
        log::info!(
            "Using username/password RPC authentication with username: {:?}",
            rpc_user.as_ref().unwrap()
        );
        (
            bitcoincore_rpc::Client::new(
                &rpc_url,
                bitcoincore_rpc::Auth::UserPass(rpc_user.unwrap(), rpc_pass.unwrap()),
            )?,
            false,
        )
    } else {
        log::info!(
            "Using Cookie authentication with cookie: {:?} {:?}",
            rpc_cookie.as_ref().unwrap(),
            rpc_url
        );
        log::info!("Connecting to RPC endpoint: {:?}", rpc_url);
        (
            bitcoincore_rpc::Client::new(
                &rpc_url,
                bitcoincore_rpc::Auth::CookieFile(PathBuf::from(
                    shellexpand::tilde(&rpc_cookie.unwrap()).to_string(),
                )),
            )?,
            true,
        )
    };

    // check if rpc is alive
    //
    // get_best_block_hash just returns a string
    let best_block_hash = match rpc.get_best_block_hash() {
        Ok(hash) => hash,
        Err(e) => {
            log::error!("Failed to get best block hash: {}", e);
            return Err(e);
        }
    };
    log::info!("Best block hash: {:?}", best_block_hash);

    // get_blockchain_info returns a json blob
    match rpc.get_blockchain_info() {
        Ok(info) => {
            log::info!("Blockchain info: {:?}", info);
        }
        Err(e) => {
            log::error!("get_blockchain_info returned an error: {:?}", e);
            if is_cookie_auth {
                log::error!(
                    "Unable to authenticate to bitcoind using a cookie file. \
                    Ensure that bitcoind is running on the same node or use \
                    rpcuser/rpcpass instead."
                );
            }
            return Err(e);
        }
    }

    Ok(rpc)
}

pub async fn check_bitcoin_node(rpc: &bitcoincore_rpc::Client, shutdown_handler: &ShutdownHandler) {
    match rpc.get_blockchain_info() {
        Ok(_) => {
            // Node is healthy
        }
        Err(e) => {
            shutdown_handler.shutdown_bitcoin_error(format!("Bitcoin node error: {}", e));
        }
    }
}
