use bitcoincore_rpc::RpcApi;
use shellexpand;
use std::path::PathBuf;

use crate::error::RpcError;

pub fn setup(
    bitcoin: String,
    rpc_port: u16,
    rpc_user: Option<String>,
    rpc_pass: Option<String>,
    rpc_cookie: Option<String>,
) -> Result<bitcoincore_rpc::Client, RpcError> {
    let rpc_url = format!("{}:{}", bitcoin, rpc_port);
    let (rpc, is_cookie_auth) = if let Some(ref user) = rpc_user {
        let pass = rpc_pass.ok_or_else(|| RpcError::MissingAuth("rpcpass".to_string()))?;
        log::info!(
            "Using username/password RPC authentication with username: {:?}",
            user
        );
        (
            bitcoincore_rpc::Client::new(
                &rpc_url,
                bitcoincore_rpc::Auth::UserPass(user.clone(), pass),
            )?,
            false,
        )
    } else {
        let cookie = rpc_cookie.ok_or_else(|| {
            RpcError::MissingAuth("rpcuser/rpcpass or rpccookie".to_string())
        })?;
        log::info!(
            "Using Cookie authentication with cookie: {:?} {:?}",
            cookie,
            rpc_url
        );
        log::info!("Connecting to RPC endpoint: {:?}", rpc_url);
        (
            bitcoincore_rpc::Client::new(
                &rpc_url,
                bitcoincore_rpc::Auth::CookieFile(PathBuf::from(
                    shellexpand::tilde(&cookie).to_string(),
                )),
            )?,
            true,
        )
    };

    // check if rpc is alive
    //
    // get_best_block_hash just returns a string
    let best_block_hash = rpc.get_best_block_hash()?;
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
            return Err(RpcError::RpcCall(e));
        }
    }

    Ok(rpc)
}
