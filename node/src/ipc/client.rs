use std::error::Error;
use std::path::PathBuf;
use std::env;
// use std::time::Duration;

use capnp_rpc::{rpc_twoparty_capnp, twoparty, RpcSystem};
use futures::FutureExt;
use tokio::net::UnixStream;
use tokio::task::{self, JoinHandle};
use tokio_util::compat::{TokioAsyncReadCompatExt, TokioAsyncWriteCompatExt};

#[allow(dead_code)]
mod chain_capnp;
mod common_capnp;
mod echo_capnp;
mod handler_capnp;
#[allow(dead_code)]
mod init_capnp;
mod mining_capnp;
#[allow(dead_code)]
mod proxy_capnp;

use chain_capnp::{
    chain::Client as ChainClient,
};

use init_capnp::init::Client as InitClient;
use proxy_capnp::thread::Client as ThreadClient;


fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes.iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>()
}


struct BitcoinRpcClient {
    ipc_task: JoinHandle<Result<(), capnp::Error>>,
    chain_interface: ChainClient,
    thread_client: ThreadClient,
    disconnector: capnp_rpc::Disconnector<twoparty::VatId>,
}

impl BitcoinRpcClient {
    // Create an IPC interface by performing the handshake with Bitcoin Core on the provided unix stream.
    pub async fn new(stream: tokio::net::UnixStream) -> Result<Self, Box<dyn std::error::Error>> {
        let (reader, writer) = stream.into_split();
        let network = Box::new(twoparty::VatNetwork::new(
            reader.compat(),
            writer.compat_write(),
            rpc_twoparty_capnp::Side::Client,
            Default::default(),
        ));

        let mut rpc = RpcSystem::new(network, None);
        let init_interface: InitClient = rpc.bootstrap(rpc_twoparty_capnp::Side::Server);
        let disconnector = rpc.get_disconnector();
        let ipc_task = task::spawn_local(rpc.map(|_| Ok(())));

        let init_req = init_interface.construct_request();
        let response = init_req.send().promise.await?;
        let thread_map = response.get()?.get_thread_map()?;

        let mk_thread_req = thread_map.make_thread_request();
        let response = mk_thread_req.send().promise.await?;
        let thread = response.get()?.get_result()?;

        let mut mk_chain_req = init_interface.make_chain_request();
        mk_chain_req.get().get_context()?.set_thread(thread.clone());
        let response = mk_chain_req.send().promise.await?;
        let chain_interface = response.get()?.get_result()?;

        // Send an init message to Core
        let mut mk_mess_req = chain_interface.init_message_request();
        mk_mess_req.get().get_context()?.set_thread(thread.clone());
        mk_mess_req
            .get()
            .set_message("Braidpool IPC connection established");
        let _ = mk_mess_req.send().promise.await?;

        Ok(Self {
            ipc_task,
            thread_client: thread,
            chain_interface,
            disconnector,
        })
    }

       pub async fn remove_transaction_from_mempool(&self, txid: &[u8]) -> Result<bool, Box<dyn Error>> {
        let mut delete_req = self.chain_interface.remove_tx_from_mempool_request();
        delete_req.get().get_context()?.set_thread(self.thread_client.clone());
        let mut reversed_txid = txid.to_vec();
        reversed_txid.reverse();
        delete_req.get().set_txid(&reversed_txid);
        let response = delete_req.send().promise.await?;
        let result = response.get()?;

        let success = result.get_result();
        Ok(success)
    }

    pub async fn get_best_block_info(&self) -> Result<(u32, Vec<u8>), Box<dyn Error>> {
        let mut height_req = self.chain_interface.get_height_request();
        height_req.get().get_context()?.set_thread(self.thread_client.clone());
        let response = height_req.send().promise.await?;
        let result = response.get()?;
        let height_i32 = result.get_result();
        let has_result = result.get_has_result();
        
        if !has_result {
            return Err("Chain height not available".into());
        }

        let height: u32 = height_i32.try_into().expect("Height is never negative.");

        let mut hash_req = self.chain_interface.get_block_hash_request();
        hash_req.get().get_context()?.set_thread(self.thread_client.clone());
        hash_req.get().set_height(height_i32);
        let response = hash_req.send().promise.await?;
        let hash = response.get()?.get_result()?.to_vec();

        Ok((height, hash))
    }

      pub async fn disconnect(self) -> Result<(), capnp::Error> {
        self.disconnector.await.unwrap();
        self.ipc_task.await.unwrap()
    }
}

async fn execute_rpc_operation(stream: tokio::net::UnixStream) -> Result<(), Box<dyn std::error::Error>> {
    let rpc = BitcoinRpcClient::new(stream).await?;
    
    match rpc.get_best_block_info().await {
        Ok((height, hash)) => {
            println!("Current blockchain height: {}", height);
            println!("Best block hash: {}", bytes_to_hex(&hash));
        }
        Err(e) => println!("Failed to get tip: {}", e),
    }

    // Test transaction removal
    let txid_hex = ""; // Replace with a valid transaction ID 
    let txid_bytes = hex::decode(txid_hex)?; 
    
    match rpc.remove_transaction_from_mempool(&txid_bytes).await {
        Ok(true) => println!("Successfully removed transaction {} from mempool", txid_hex),
        Ok(false) => println!("Transaction {} was not found in mempool or could not be removed", txid_hex),
        Err(e) => println!("Failed to remove transaction: {}", e),
    }


    println!("Disconnecting immediately...");
    rpc.disconnect().await?;
    println!("Connection closed successfully");
    
    Ok(())
}


#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} /path/to/bitcoin-node/unix/socket", args[0]);
        eprintln!("Example: {} /tmp/bitcoin-ipc-socket", args[0]);
        return Ok(());
    }

    let socket_path = args.last().expect("Just checked.");
    println!("Connecting to Bitcoin IPC socket: {}", socket_path);
    
    // Check if socket exists
    let path = PathBuf::from(socket_path);
    if !path.exists() {
        eprintln!("Socket path does not exist: {}", socket_path);
        eprintln!("Make sure Bitcoin Core is running with IPC enabled.");
        return Err("Please provide the correct socket path".into());
    }
    
    let stream = UnixStream::connect(&socket_path).await?;
    println!("Socket connection established...");

    tokio::task::LocalSet::new()
        .run_until(execute_rpc_operation(stream))
        .await
}