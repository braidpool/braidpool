use bitcoin::absolute::Time;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::Error;
use bitcoin::ecdsa::Signature;
use bitcoin::io::{self, BufRead, Write};
use core::str::FromStr;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct UnCommittedMetadata {
    pub extra_nonce: i32,
    pub broadcast_timestamp: Time,
    pub signature: Signature,
}

impl Encodable for UnCommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.extra_nonce.consensus_encode(w)?;
        len += self
            .broadcast_timestamp
            .to_consensus_u32()
            .consensus_encode(w)?;
        len += self.signature.to_string().consensus_encode(w)?;
        Ok(len)
    }
}

impl Decodable for UnCommittedMetadata {
    fn consensus_decode<R: BufRead + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let extra_nonce = i32::consensus_decode(r)?;
        let broadcast_timestamp = Time::from_consensus(u32::consensus_decode(r).unwrap()).unwrap();
        let signature = Signature::from_str(&String::consensus_decode(r).unwrap()).unwrap();

        Ok(UnCommittedMetadata {
            extra_nonce,
            broadcast_timestamp,
            signature,
        })
    }
}
