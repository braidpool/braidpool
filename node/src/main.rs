use clap::Parser;
use std::error::Error;
use std::fs;
use std::net::ToSocketAddrs;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

mod block_template;
mod cli;
mod connection;
mod protocol;
mod rpc;
mod zmq;

/// Entry point of the Bitcoin protocol application.
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = cli::Cli::parse();

    setup_logging();
    setup_tracing()?;

    // Expand and validate data directory
    let datadir = shellexpand::full(args.datadir.to_str().unwrap())?;
    validate_data_directory(&datadir)?;

    // Set up RPC and ZMQ for communication
    let rpc = rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
        args.rpccookie,
    )?;

    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);
    let (block_template_tx, block_template_rx) = mpsc::channel(1);

    tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc.clone(), block_template_tx));
    tokio::spawn(block_template::consumer(block_template_rx));

    // Connect to manually added nodes
    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            if let Err(e) = connect_to_node(node).await {
                log::warn!("Failed to connect to node {}: {:?}", node, e);
            }
        }
    }

    // Start TCP listener for incoming connections
    log::info!("Binding to {}", args.bind);
    let listener = TcpListener::bind(&args.bind).await?;
    accept_connections(listener).await
}

/// Validates and ensures the data directory exists.
fn validate_data_directory(datadir: &str) -> Result<(), Box<dyn Error>> {
    match fs::metadata(datadir) {
        Ok(m) if !m.is_dir() => {
            log::error!("Data directory {} exists but is not a directory", datadir);
            Err("Invalid data directory".into())
        }
        Ok(_) => {
            log::info!("Using existing data directory: {}", datadir);
            Ok(())
        }
        Err(_) => {
            log::info!("Creating data directory: {}", datadir);
            fs::create_dir_all(datadir)?;
            Ok(())
        }
    }
}

/// Establishes a connection to a specified node.
async fn connect_to_node(node: &str) -> Result<(), Box<dyn Error>> {
    log::info!("Attempting connection to node: {}", node);
    let stream = TcpStream::connect(node).await?;
    let (r, w) = stream.into_split();
    let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
    let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());

    let mut conn = connection::Connection::new(framed_reader, framed_writer);
    if let Ok(mut addr_iter) = node.to_socket_addrs() {
        if let Some(addr) = addr_iter.next() {
            tokio::spawn(async move {
                if let Err(_) = conn.start_from_connect(&addr).await {
                    log::warn!("Peer {} closed connection", addr);
                }
            });
        }
    }
    Ok(())
}

/// Accepts and handles incoming TCP connections.
async fn accept_connections(listener: TcpListener) -> Result<(), Box<dyn Error>> {
    loop {
        log::info!("Waiting for incoming connections...");
        match listener.accept().await {
            Ok((stream, _)) => {
                let addr = match stream.peer_addr() {
                    Ok(a) => a,
                    Err(e) => {
                        log::error!("Failed to get peer address: {:?}", e);
                        continue;
                    }
                };

                log::info!("Accepted connection from {}", addr);
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());

                let mut conn = connection::Connection::new(framed_reader, framed_writer);
                tokio::spawn(async move {
                    if conn.start_from_accept().await.is_err() {
                        log::warn!("Peer {} closed connection", addr);
                    }
                });
            }
            Err(e) => log::error!("Failed to accept client: {:?}", e),
        }
    }
}

/// Configures logging for the application.
fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

/// Sets up tracing for better debugging and monitoring.
fn setup_tracing() -> Result<(), Box<dyn Error>> {
    let filter = tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();
    tracing::subscriber::set_global_default(subscriber)?;
    Ok(())
}
