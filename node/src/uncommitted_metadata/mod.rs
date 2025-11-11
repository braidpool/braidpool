use bitcoin::absolute::Time;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::Error;
use bitcoin::ecdsa::Signature;
use bitcoin::io::{self, BufRead, Write};
use bitcoin::EcdsaSighashType;
use core::str::FromStr;
use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct UnCommittedMetadata {
    pub extra_nonce_1: u32,
    pub extra_nonce_2: u32,
    pub broadcast_timestamp: Time,
    pub signature: Signature,
}
impl Default for UnCommittedMetadata {
    fn default() -> Self {
        let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
        let default_sig = Signature {
            signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
            sighash_type: EcdsaSighashType::All,
        };
        Self {
            extra_nonce_1: 0,
            extra_nonce_2: 0,
            broadcast_timestamp: bitcoin::blockdata::locktime::absolute::MedianTimePast::MIN,
            signature: default_sig,
        }
    }
}
impl Encodable for UnCommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.extra_nonce_1.consensus_encode(w)?;
        len += self.extra_nonce_2.consensus_encode(w)?;
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
        let extra_nonce_1 = u32::consensus_decode(r)?;
        let extra_nonce_2 = u32::consensus_decode(r)?;
        let broadcast_timestamp = Time::from_consensus(u32::consensus_decode(r).unwrap()).unwrap();
        let signature = Signature::from_str(&String::consensus_decode(r).unwrap()).unwrap();

        Ok(UnCommittedMetadata {
            extra_nonce_1,
            extra_nonce_2,
            broadcast_timestamp,
            signature,
        })
    }
}
