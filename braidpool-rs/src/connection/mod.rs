use std::error::Error;
use std::io;
use tokio::io::AsyncWriteExt;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
//use tokio::net::TcpStream;

// mod protocol;
//use protocol::Protocol;

// pub struct Connection {
//     reader: OwnedReadHalf,
//     writer: OwnedWriteHalf,
// }

// pub fn build_connection(stream: TcpStream) -> Connection {
//     let (reader, writer) = stream.into_split();
//     Connection { reader, writer }
// }

pub async fn start_from_connect(
    reader: OwnedReadHalf,
    writer: &mut OwnedWriteHalf,
) -> Result<(), Box<dyn Error>> {
    println!("Starting from connect");
    let _ = start_read_loop(reader).await;
    println!("read loop start returned..");
    let _ = writer.write_all(b"ping").await;
    Ok(())
}

pub async fn start_from_accept(
    reader: OwnedReadHalf,
    writer: &mut OwnedWriteHalf,
) -> Result<(), Box<dyn Error>> {
    println!("Starting from accept");
    let _ = start_read_loop(reader).await;
    let _ = writer.write_all(b"ping from accept").await;
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

pub async fn start_read_loop(reader: OwnedReadHalf) -> Result<(), Box<dyn Error>> {
    tokio::spawn(async move {
        println!("Start read loop....");
        let mut msg = vec![0; 1024];
        loop {
            let _ = reader.readable().await;
            println!("Reader ready....");
            match reader.try_read(&mut msg) {
                Ok(n) => {
                    msg.truncate(n);
                    println!("Message received... {:?}", msg);
                    break;
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
