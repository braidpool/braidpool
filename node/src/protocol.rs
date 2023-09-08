extern crate flexbuffers;
extern crate serde;
// #[macro_use]
// extern crate serde_derive;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub enum Message {
    Ping { message: String },
}

pub trait Protocol {
    fn start(&mut self) -> Option<Message>;
    fn received(&mut self, message: &Message) -> Option<Message>;
}

impl Protocol for Message {
    fn start(&mut self) -> Option<Message> {
        Some(Message::Ping {
            message: String::from("ping"),
        })
    }

    fn received(&mut self, _message: &Message) -> Option<Message> {
        Some(Message::Ping {
            message: String::from("pong"),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Message;
    use crate::protocol::serde::Serialize;
    use bytes::Bytes;

    #[test]
    fn it_serialized_ping_message() {
        let ping_message = Message::Ping {
            message: String::from("ping"),
        };
        let mut s = flexbuffers::FlexbufferSerializer::new();
        ping_message.serialize(&mut s).unwrap();
        let b = Bytes::from(s.take_buffer());

        let m: Message = flexbuffers::from_slice(&b).unwrap();
        assert_eq!(m, ping_message)
    }
}
