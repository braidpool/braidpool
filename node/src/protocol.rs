use bytes::Bytes;
use std::error::Error;
extern crate flexbuffers;
extern crate serde;
// #[macro_use]
// extern crate serde_derive;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct PingMessage {
    pub message: String,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct HandshakeMessage {
    pub message: String,
    pub version: String,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub enum Message {
    Ping(PingMessage),
    Handshake(HandshakeMessage),
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

    pub fn response_for_received(&self) -> Option<Message> {
        match self {
            Message::Ping(m) => m.response_for_received(),
            Message::Handshake(m) => m.response_for_received(),
        }
    }
}

pub trait ProtocolMessage
where
    Self: Sized,
{
    fn start() -> Option<Message>;
    fn response_for_received(&self) -> Option<Message>;
}

impl ProtocolMessage for PingMessage {
    fn start() -> Option<Message> {
        Some(Message::Ping(PingMessage {
            message: String::from("ping"),
        }))
    }

    fn response_for_received(&self) -> Option<Message> {
        println!("Received {:?}", self.message);
        if self.message == "ping" {
            Some(Message::Ping(PingMessage {
                message: String::from("pong"),
            }))
        } else {
            None
        }
    }
}

impl ProtocolMessage for HandshakeMessage {
    fn start() -> Option<Message> {
        Some(Message::Handshake(HandshakeMessage {
            message: String::from("helo"),
            version: String::from("0.1.0"),
        }))
    }

    fn response_for_received(&self) -> Option<Message> {
        println!("Received {:?}", self.version);
        match self.message.as_str() {
            "helo" => Some(Message::Handshake(HandshakeMessage {
                message: String::from("oleh"),
                version: String::from("0.1.0"),
            })),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Message::{self, Ping};
    use super::PingMessage;
    use super::ProtocolMessage;
    use crate::protocol::serde::Serialize;
    use bytes::Bytes;

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
        let start_message = PingMessage::start().unwrap();
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
            Message::Ping(PingMessage {
                message: String::from("pong")
            })
        );
    }
}
