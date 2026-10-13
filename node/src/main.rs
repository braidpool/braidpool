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

    let rpc = rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
        args.rpccookie,
    )?;
    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);

    let (block_template_tx, block_template_rx) = mpsc::channel(1);
    tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, block_template_tx));
    tokio::spawn(block_template::consumer(block_template_rx));

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
                let addr = match stream.peer_addr() {
                    Ok(addr) => addr,
                    Err(e) => {
                        log::warn!("Failed to get peer address: {:?}", e);
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
                        log::warn!("Peer {} closed connection", addr)
                    }
                });
            }
            Err(e) => log::error!("couldn't get client: {:?}", e),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_accept_loop_continues_after_peer_disconnect() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let local_addr = listener.local_addr().unwrap();

        let (accepted_tx, mut accepted_rx) = tokio::sync::mpsc::channel(10);
        let (shutdown_tx, mut shutdown_rx) = tokio::sync::oneshot::channel::<()>();

        // Spawn simulated accept loop matching the logic in main()
        let accept_task = tokio::spawn(async move {
            loop {
                tokio::select! {
                    _ = &mut shutdown_rx => break,
                    res = listener.accept() => {
                        match res {
                            Ok((stream, _)) => {
                                let addr = match stream.peer_addr() {
                                    Ok(addr) => addr,
                                    Err(e) => {
                                        log::warn!("Failed to get peer address: {:?}", e);
                                        continue;
                                    }
                                };
                                let _ = accepted_tx.send(addr).await;
                            }
                            Err(e) => {
                                log::error!("couldn't get client: {:?}", e);
                            }
                        }
                    }
                }
            }
        });

        // Client 1: Connects and drops immediately (simulating early disconnect)
        let client1 = tokio::spawn(async move {
            let stream = TcpStream::connect(local_addr).await.unwrap();
            drop(stream);
        });
        client1.await.unwrap();

        // Client 2: Normal connection that stays open long enough to be recorded
        let client2 = tokio::spawn(async move {
            let stream = TcpStream::connect(local_addr).await.unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
            drop(stream);
        });

        // The accept loop must accept the second client without having crashed
        let second_addr =
            tokio::time::timeout(tokio::time::Duration::from_secs(2), accepted_rx.recv())
                .await
                .expect("Accept loop timed out or terminated early")
                .expect("Channel closed unexpectedly");

        assert_eq!(second_addr.ip(), local_addr.ip());

        client2.await.unwrap();
        let _ = shutdown_tx.send(());
        accept_task.await.unwrap();
    }
}
