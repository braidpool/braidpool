use bytes::Bytes;
use std::error::Error;
extern crate flexbuffers;
extern crate serde;
// #[macro_use]
// extern crate serde_derive;
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;

mod handshake;
mod heartbeat;
mod ping;

pub use handshake::HandshakeMessage;
pub use heartbeat::HeartbeatMessage;
pub use ping::PingMessage;

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub enum Message {
    Ping(PingMessage),
    Handshake(HandshakeMessage),
    Heartbeat(HeartbeatMessage),
}

impl Message {
    pub fn as_bytes(&self) -> Option<Bytes> {
        let mut s = flexbuffers::FlexbufferSerializer::new();
        self.serialize(&mut s).unwrap();
        Some(Bytes::from(s.take_buffer()))
    }

    pub fn from_bytes(b: &[u8]) -> Result<Self, Box<dyn Error>> {
        Ok(flexbuffers::from_slice(b)?)
    }

    pub fn response_for_received(&self) -> Result<Option<Message>, &'static str> {
        match self {
            Message::Ping(m) => m.response_for_received(),
            Message::Handshake(m) => m.response_for_received(),
            Message::Heartbeat(m) => m.response_for_received(),
        }
    }
}

pub trait ProtocolMessage
where
    Self: Sized,
{
    fn start(addr: &SocketAddr) -> Option<Message>;
    fn response_for_received(&self) -> Result<Option<Message>, &'static str>;
}

#[cfg(test)]
mod tests {
    use super::Message;
    use super::PingMessage;
    use super::ProtocolMessage;
    use crate::protocol::serde::Serialize;
    use bytes::Bytes;
    use std::net::SocketAddr;
    use std::str::FromStr;

    #[test]
    fn it_serialized_ping_message() {
        let ping_message = Message::Ping(PingMessage {
            message: String::from("ping"),
        });
        let mut s = flexbuffers::FlexbufferSerializer::new();
        ping_message.serialize(&mut s).unwrap();
        let b = Bytes::from(s.take_buffer());

        let msg = Message::from_bytes(&b).unwrap();
        assert_eq!(msg, ping_message);
    }

    #[test]
    fn it_matches_start_message_for_ping() {
        let addr = SocketAddr::from_str("127.0.0.1:25188").unwrap();
        let start_message = PingMessage::start(&addr).unwrap();
        assert_eq!(
            start_message,
            Message::Ping(PingMessage {
                message: String::from("ping")
            })
        );
    }

    #[test]
    fn it_invoked_received_message_after_deseralization() {
        let b: Bytes = Message::Ping(PingMessage {
            message: String::from("ping"),
        })
        .as_bytes()
        .unwrap();

        let msg: Message = Message::from_bytes(&b).unwrap();

        let response = msg.response_for_received().unwrap();
        assert_eq!(
            response,
            Some(Message::Ping(PingMessage {
                message: String::from("pong")
            }))
        );
    }
}
