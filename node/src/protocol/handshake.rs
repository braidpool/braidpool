use super::{Message, ProtocolMessage};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct HandshakeMessage {
    pub message: String,
    pub version: String,
}

impl ProtocolMessage for HandshakeMessage {
    fn start() -> Option<Message> {
        Some(Message::Handshake(HandshakeMessage {
            message: String::from("helo"),
            version: String::from("0.1.0"),
        }))
    }

    fn response_for_received(&self) -> Result<Option<Message>, &'static str> {
        println!("Received {:?}", self);
        match self {
            HandshakeMessage { message, version } if message == "helo" && version == "0.1.0" => {
                Ok(Some(Message::Handshake(HandshakeMessage {
                    message: String::from("oleh"),
                    version: String::from("0.1.0"),
                })))
            }
            HandshakeMessage { message, version } if message == "oleh" && version == "0.1.0" => {
                Ok(None)
            }
            _ => Err("Bad message"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::protocol::{HandshakeMessage, Message, ProtocolMessage};

    #[test]
    fn it_matches_start_message_for_handshake() {
        let start_message = HandshakeMessage::start().unwrap();
        assert_eq!(
            start_message,
            Message::Handshake(HandshakeMessage {
                message: String::from("helo"),
                version: String::from("0.1.0"),
            })
        );
    }

    #[test]
    fn it_matches_response_message_for_correct_handshake_start() {
        let start_message = HandshakeMessage::start().unwrap();
        let response = start_message.response_for_received().unwrap();
        assert_eq!(
            response,
            Some(Message::Handshake(HandshakeMessage {
                message: String::from("oleh"),
                version: String::from("0.1.0"),
            }))
        );
    }

    #[test]
    fn it_matches_error_response_message_for_incorrect_handshake_start() {
        let start_message = Message::Handshake(HandshakeMessage {
            message: String::from("bad-message"),
            version: String::from("0.1.0"),
        });

        let response = start_message.response_for_received();
        assert_eq!(response, Err("Bad message"));
    }

    #[test]
    fn it_matches_error_response_message_for_incorrect_handshake_version() {
        let start_message = Message::Handshake(HandshakeMessage {
            message: String::from("helo"),
            version: String::from("0.2.0"),
        });

        let response = start_message.response_for_received();
        assert_eq!(response, Err("Bad message"));
    }
}
