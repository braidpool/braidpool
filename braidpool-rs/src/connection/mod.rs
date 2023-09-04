use std::error::Error;
use std::io;
use tokio::io::AsyncWriteExt;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::mpsc;
//use tokio::net::TcpStream;

//mod protocol;

// pub struct Connection {
//     reader: OwnedReadHalf,
//     writer: OwnedWriteHalf,
// }

// pub fn build_connection(stream: TcpStream) -> Connection {
//     let (reader, writer) = stream.into_split();
//     Connection { reader, writer }
// }

const CHANNEL_CAPACITY: usize = 32;

pub async fn start_from_connect(
    reader: OwnedReadHalf,
    writer: OwnedWriteHalf,
) -> Result<(), Box<dyn Error>> {
    println!("Starting from connect");
    let (channel_sender, channel_receiver) = mpsc::channel(CHANNEL_CAPACITY);
    start_read_loop(reader, channel_sender).await?;
    println!("read loop started in connect..");
    let _ = start_connect_protocols(writer, channel_receiver).await;
    Ok(())
}

pub async fn start_from_accept(
    reader: OwnedReadHalf,
    writer: OwnedWriteHalf,
) -> Result<(), Box<dyn Error>> {
    println!("Starting from accept");
    let (channel_sender, channel_receiver) = mpsc::channel(CHANNEL_CAPACITY);
    let _ = start_read_loop(reader, channel_sender).await;
    println!("read loop started in accept..");
    let _ = start_accept_protocols(writer, channel_receiver).await;
    Ok(())
}

// pub async fn _stop(connection: Connection) -> Result<(), Box<dyn Error>> {
//     drop(connection.writer);
//     Ok(())
// }

// pub async fn send(writer: &mut OwnedWriteHalf, msg: &[u8]) -> Result<(), Box<dyn Error>> {
//     let _ = writer.write_all(msg).await;
//     Ok(())
// }

pub async fn start_read_loop(
    reader: OwnedReadHalf,
    channel_sender: mpsc::Sender<Vec<u8>>,
) -> Result<(), Box<dyn Error>> {
    tokio::spawn(async move {
        println!("Start read loop....");
        loop {
            let _ = reader.readable().await;
            let mut msg = vec![0; 1024];
            match reader.try_read(&mut msg) {
                Ok(0) => {
                    // TODO - this is a hack. Once we start using
                    // framed readers we need to take a look at this
                    // again.
                    println!("Peer disconnected");
                    break;
                }
                Ok(n) => {
                    msg.truncate(n);
                    println!("Message received... {:?}", msg);
                    println!("Sending to channel");
                    channel_sender.send(msg).await.unwrap();
                }
                Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                    continue;
                }
                Err(_) => {
                    panic!("Error reading from stream");
                }
            }
        }
    });
    Ok(())
}

async fn start_accept_protocols(
    mut writer: OwnedWriteHalf,
    mut channel_receiver: mpsc::Receiver<Vec<u8>>,
) -> Result<(), Box<dyn Error>> {
    println!("Starting accept protocols......");
    tokio::spawn(async move {
        println!("Starting channel receiver...");
        while let Some(message) = channel_receiver.recv().await {
            println!("GOT = {:?}", message);
            let _ = writer.write_all(b"pong\n").await;
        }
    });
    Ok(())
}

async fn start_connect_protocols(
    mut writer: OwnedWriteHalf,
    mut channel_receiver: mpsc::Receiver<Vec<u8>>,
) -> Result<(), Box<dyn Error>> {
    writer.write_all(b"ping\n").await?;
    println!("Ping sent...");
    tokio::spawn(async move {
        while let Some(message) = channel_receiver.recv().await {
            println!("GOT = {:?}", message);
            //let _ = writer.write_all(b"ping").await;
        }
    });
    Ok(())
}
