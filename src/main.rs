use clap::Parser;
use std::error::Error;
use std::fs;
use std::net::ToSocketAddrs;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio::task::JoinSet;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};
use anyhow::{Context, Result};
use tracing::{info, error, warn};

mod block_template;
mod braid;
mod cli;
mod connection;
mod protocol;
mod rpc;
mod zmq;

#[tokio::main]
async fn main() -> Result<()> {
    let args = cli::Cli::parse();

    setup_logging();
    setup_tracing().context("Failed to set up tracing")?;

    let datadir = shellexpand::full(args.datadir.to_str().unwrap())
        .context("Failed to expand data directory path")?;
    
    fs::create_dir_all(&*datadir).or_else(|err| {
        error!("Error creating data directory {}: {}", datadir, err);
        Err(err)
    })?;

    info!("Using data directory: {}", datadir);

    let rpc = rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
        args.rpccookie,
    )
    .context("Failed to set up RPC")?;
    
    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);
    let (block_template_tx, block_template_rx) = mpsc::channel(1);
    
    let mut tasks = JoinSet::new();

    tasks.spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, block_template_tx));
    tasks.spawn(block_template::consumer(block_template_rx));

    if let Some(addnodes) = args.addnode {
        for node in addnodes.iter() {
            let node = node.clone();
            tasks.spawn(async move {
                match TcpStream::connect(&node).await {
                    Ok(stream) => {
                        let (r, w) = stream.into_split();
                        let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                        let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
                        let mut conn = connection::Connection::new(framed_reader, framed_writer);

                        if let Ok(mut addr_iter) = node.to_socket_addrs() {
                            if let Some(addr) = addr_iter.next() {
                                if conn.start_from_connect(&addr).await.is_err() {
                                    warn!("Peer {} closed connection", addr);
                                }
                            }
                        }
                    }
                    Err(e) => error!("Failed to connect to {}: {:?}", node, e),
                }
            });
        }
    }

    info!("Binding to {}", args.bind);
    let listener = TcpListener::bind(&args.bind).await?;

    let server_task = tokio::spawn(async move {
        loop {
            match listener.accept().await {
                Ok((stream, _)) => {
                    let addr = match stream.peer_addr() {
                        Ok(a) => a,
                        Err(e) => {
                            error!("Failed to get peer address: {:?}", e);
                            continue;
                        }
                    };

                    info!("Accepted connection from {}", addr);

                    let (r, w) = stream.into_split();
                    let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                    let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
                    let mut conn = connection::Connection::new(framed_reader, framed_writer);

                    tokio::spawn(async move {
                        if conn.start_from_accept().await.is_err() {
                            warn!("Peer {} closed connection", addr);
                        }
                    });
                }
                Err(e) => error!("Couldn't accept client: {:?}", e),
            }
        }
    });

    tasks.spawn(server_task);

    tokio::select! {
        _ = tasks.join_next() => {
            error!("A task unexpectedly finished, shutting down...");
        }
        _ = shutdown_signal() => {
            info!("Shutdown signal received, terminating...");
        }
    }

    Ok(())
}

fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

fn setup_tracing() -> Result<()> {
    let filter = tracing_subscriber::EnvFilter::from_default_env()
        .add_directive("chat=info".parse()?);

    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    tracing::subscriber::set_global_default(subscriber)
        .context("Setting default subscriber failed")?;

    Ok(())
}

async fn shutdown_signal() {
    tokio::signal::ctrl_c()
        .await
        .expect("Failed to listen for shutdown signal");
}
