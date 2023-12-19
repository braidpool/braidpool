use bitcoincore_rpc::RpcApi;
use shellexpand;
use std::path::PathBuf;

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
            "Using Cookie authentication with cookie: {:?}",
            rpc_cookie.as_ref().unwrap()
        );
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
    if let Err(e) = rpc.get_blockchain_info() {
        log::error!("{:?}", e);
        if is_cookie_auth {
            log::error!(
                "Unable to authenticate to bitcoind using a cookie file. \
                Ensure that bitcoind is running on the same node or use \
                rpcuser/rpcpass instead."
            );
        }
        std::process::exit(1);
    }

    Ok(rpc)
}
