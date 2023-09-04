use std::error::Error;

pub trait Protocol {
    fn start(&mut self) -> Result<(), Box<dyn Error>>;
}

pub struct Handshake<'a> {
    pub connection: &'a mut Connection,
}

impl<'a> Protocol for Handshake<'a> {
    fn start(&mut self) -> Result<(), Box<dyn Error>> {
        let _ = self.connection.send(b"ping");
        Ok(())
    }
}
