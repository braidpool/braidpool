pub fn setup(
    bitcoin: String,
    rpc_port: u16,
    rpc_user: String,
    rpc_pass: String,
) -> Result<bitcoincore_rpc::Client, bitcoincore_rpc::Error> {
    let rpc_url = format!("{}:{}", bitcoin, rpc_port);
    bitcoincore_rpc::Client::new(
        &rpc_url,
        bitcoincore_rpc::Auth::UserPass(rpc_user, rpc_pass),
    )
}
