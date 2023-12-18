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
    println!("{:?}", rpc_user);
    let rpc = if rpc_user.is_some() {
        log::info!(
            "Using username/password RPC authentication with username: {:?}",
            rpc_user.as_ref().unwrap()
        );
        bitcoincore_rpc::Client::new(
            &rpc_url,
            bitcoincore_rpc::Auth::UserPass(rpc_user.unwrap(), rpc_pass.unwrap()),
        )?
    } else {
        log::info!(
            "Using Cookie authentication with cookie: {:?}",
            rpc_cookie.as_ref().unwrap()
        );
        bitcoincore_rpc::Client::new(
            &rpc_url,
            bitcoincore_rpc::Auth::CookieFile(PathBuf::from(
                shellexpand::tilde(&rpc_cookie.unwrap()).to_string(),
            )),
        )?
    };

    // check if rpc is alive
    let res = rpc.get_blockchain_info()?;
    log::info!("{:?}", res);

    Ok(rpc)
}
