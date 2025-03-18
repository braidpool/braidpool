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

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // Parse command-line arguments
    let args = cli::Cli::parse();

    // Initialize logging and tracing for debugging and monitoring
    setup_logging();
    setup_tracing()?;

    // Expand and validate the data directory path
    let datadir = shellexpand::full(args.datadir.to_str().unwrap()).unwrap();
    match fs::metadata(&*datadir) {
        Ok(metadata) => {
            if !metadata.is_dir() {
                log::error!("Data directory {} exists but is not a directory", datadir);
            }
            log::info!("Using existing data directory: {}", datadir);
        }
        Err(_) => {
            log::info!("Creating data directory: {}", datadir);
            fs::create_dir_all(&*datadir)?;
        }
    }

    // Setup the RPC connection with Bitcoin Core
    let rpc = rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
        args.rpccookie,
    )?;

    // Define the ZMQ URL for receiving hash block notifications
    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);

    // Create an asynchronous channel for handling block template updates
    let (block_template_tx, block_template_rx) = mpsc::channel(1);

    // Spawn a task to listen for new blocks via ZeroMQ and handle updates
    tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, block_template_tx));

    // Spawn a consumer task to process received block templates
    tokio::spawn(block_template::consumer(block_template_rx));

    // If additional nodes are specified, establish connections with them
    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            // Attempt to connect to the specified node asynchronously
            let stream = TcpStream::connect(node).await.expect("Error connecting");

            // Split the TCP stream into reader and writer components
            let (r, w) = stream.into_split();
            let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
            let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());

            // Initialize a connection handler
            let mut conn = connection::Connection::new(framed_reader, framed_writer);

            // Resolve the node address and spawn a connection task
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

    // Bind the server to the specified address and start listening for connections
    log::info!("Binding to {}", args.bind);
    let listener = TcpListener::bind(&args.bind).await?;

    loop {
        // Wait for an inbound TCP connection
        log::info!("Waiting for incoming connections...");

        match listener.accept().await {
            Ok((stream, _)) => {
                let addr = stream.peer_addr()?;
                log::info!("Accepted connection from {}", addr);

                // Split the stream for asynchronous reading and writing
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());

                // Initialize a connection handler for the new client
                let mut conn = connection::Connection::new(framed_reader, framed_writer);

                // Spawn a task to manage the client connection
                tokio::spawn(async move {
                    if conn.start_from_accept().await.is_err() {
                        log::warn!("Peer {} closed connection", addr)
                    }
                });
            }
            Err(e) => log::error!("Error accepting client connection: {:?}", e),
        }
    }
}

/// Initializes logging using the `env_logger` crate.
fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

/// Configures and initializes tracing for structured logging.
fn setup_tracing() -> Result<(), Box<dyn Error>> {
    // Create a filter to control verbosity based on environment variables
    let filter =
        tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);

    // Build a tracing subscriber with the specified filter
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    // Set the subscriber as the global default for structured logging
    tracing::subscriber::set_global_default(subscriber)
        .expect("Failed to set the default tracing subscriber");

    Ok(())
}
