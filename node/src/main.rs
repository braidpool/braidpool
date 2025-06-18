use clap::Parser;
use std::error::Error;
use std::fs;
use std::net::ToSocketAddrs;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

mod block_template;
mod braid;
mod cli;
mod connection;
mod protocol;
mod rpc;
mod zmq;
mod ipc;

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

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = cli::Cli::parse();

    setup_logging();
    setup_tracing()?;

    let datadir = shellexpand::full(args.datadir.to_str().unwrap()).unwrap();
    match fs::metadata(&*datadir) {
        Ok(m) => {
            if !m.is_dir() {
                log::error!("Data directory {} exists but is not a directory", datadir);
            }
            log::info!("Using existing data directory: {}", datadir);
        }
        Err(_) => {
            log::info!("Creating data directory: {}", datadir);
            fs::create_dir_all(&*datadir)?;
        }
    }

    if args.ipc {
        log::info!("Socket path: {}", args.ipc_socket);
        
        let (ipc_template_tx, ipc_template_rx) = mpsc::channel::<Vec<u8>>(1);
        
        let ipc_socket_path = args.ipc_socket.clone();
        
        tokio::task::spawn_blocking(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("Failed to create tokio runtime");
            
            rt.block_on(async {
                let local_set = tokio::task::LocalSet::new();
                
                local_set.run_until(async {
                    let listener_task = tokio::task::spawn_local({
                        let ipc_socket_path = ipc_socket_path.clone();
                        let ipc_template_tx = ipc_template_tx.clone();
                        async move {
                            loop {
                                match ipc::ipc_block_listener(ipc_socket_path.clone(), ipc_template_tx.clone()).await {
                                    Ok(_) => {
                                        break;
                                    }
                                    Err(e) => {
                                        log::error!("IPC block listener failed: {}", e);
                                        log::info!("Restarting IPC listener in 10 seconds...");
                                        tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
                                    }
                                }
                            }
                        }
                    });
                    
                    let consumer_task = tokio::task::spawn_local(async move {
                        ipc_template_consumer(ipc_template_rx).await;
                    });
                    
                    tokio::select! {
                        _ = listener_task => log::info!("IPC listener completed"),
                        _ = consumer_task => log::info!("IPC consumer completed"),
                    }
                }).await;
            });
        });
    } else {
        log::info!("Using ZMQ for Bitcoin Core communication");
        log::info!("ZMQ URL: tcp://{}:{}", args.bitcoin, args.zmqhashblockport);
            let rpc = rpc::setup(
            args.bitcoin.clone(),
            args.rpcport,
            args.rpcuser,
            args.rpcpass,
            args.rpccookie,
        )?;
        let (zmq_template_tx, zmq_template_rx) = mpsc::channel(1);
        let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);
        tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, zmq_template_tx));
        tokio::spawn(block_template::consumer(zmq_template_rx));
    }
    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            //log::info!("Connecting to node: {:?}", node);
            let stream = TcpStream::connect(node).await.expect("Error connecting");
            let (r, w) = stream.into_split();
            let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
            let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
            let mut conn = connection::Connection::new(framed_reader, framed_writer);
            if let Ok(addr_iter) = node.to_socket_addrs() {
                if let Some(addr) = addr_iter.into_iter().next() {
                    tokio::spawn(async move {
                        if conn.start_from_connect(&addr).await.is_err() {
                            log::warn!("Peer {} closed connection", addr)
                        }
                    });
                }
            }
        }
    }

    log::info!("Binding to {}", args.bind);
    let listener = TcpListener::bind(&args.bind).await?;
    loop {
        // Asynchronously wait for an inbound TcpStream.
        log::info!("Starting accept");
        match listener.accept().await {
            Ok((stream, _)) => {
                let addr = stream.peer_addr()?;
                log::info!("Accepted connection from {}", addr);
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
                let mut conn = connection::Connection::new(framed_reader, framed_writer);

                tokio::spawn(async move {
                    if conn.start_from_accept().await.is_err() {
                        log::warn!("Peer {} closed connection", addr)
                    }
                });
            }
            Err(e) => log::error!("couldn't get client: {:?}", e),
        }
    }
}

async fn ipc_template_consumer(mut template_rx: mpsc::Receiver<Vec<u8>>) {    
    while let Some(template_bytes) = template_rx.recv().await {
        if template_bytes.len() > 0 {
            // Process the template bytes as needed
            // For example, you could deserialize it or log its contents
            // let hex_string = bytes_to_hex(&template_bytes);
            // log::info!("Template in hex: {}", hex_string);
        } else {
            log::warn!("IPC template too short: {} bytes", template_bytes.len());
        }
    }
}

fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

fn setup_tracing() -> Result<(), Box<dyn Error>> {
    // Create a filter for controlling the verbosity of tracing output
    let filter =
        tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);

    // Build a `tracing` subscriber with the specified filter
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    // Set the subscriber as the global default for tracing
    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber failed");

    Ok(())
}