use bitcoin::absolute::Time;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::encode::Error;
use bitcoin::io::{self, Read, Write};
use bitcoin::secp256k1::schnorr::Signature;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Uncommitted bead fields authenticated by a BIP340 Schnorr signature.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct UnCommittedMetadata {
    pub extra_nonce_1: u64,
    pub extra_nonce_2: u64,
    pub broadcast_timestamp: Time,
    #[serde(
        serialize_with = "serialize_schnorr",
        deserialize_with = "deserialize_schnorr"
    )]
    pub signature: Signature,
}

fn serialize_schnorr<S>(sig: &Signature, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_str(&hex::encode(sig.as_ref()))
}

fn deserialize_schnorr<'de, D>(deserializer: D) -> Result<Signature, D::Error>
where
    D: Deserializer<'de>,
{
    let hex_str = String::deserialize(deserializer)?;
    let bytes = hex::decode(&hex_str).map_err(serde::de::Error::custom)?;
    Signature::from_slice(&bytes).map_err(serde::de::Error::custom)
}

impl Default for UnCommittedMetadata {
    fn default() -> Self {
        Self {
            extra_nonce_1: 0,
            extra_nonce_2: 0,
            broadcast_timestamp: Time::MIN,
            signature: Signature::from_slice(&[0u8; 64])
                .expect("64 zero bytes are a well-formed Schnorr signature encoding"),
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
        w.write_all(self.signature.as_ref())?;
        len += 64;
        Ok(len)
    }
}

impl Decodable for UnCommittedMetadata {
    fn consensus_decode<R: Read + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let extra_nonce_1 = u64::consensus_decode(r)?;
        let extra_nonce_2 = u64::consensus_decode(r)?;
        let broadcast_timestamp =
            Time::from_consensus(u32::consensus_decode(r)?).map_err(|_| {
                Error::from(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "invalid broadcast_timestamp in UnCommittedMetadata",
                ))
            })?;
        let mut sig_bytes = [0u8; 64];
        r.read_exact(&mut sig_bytes).map_err(Error::from)?;
        let signature = Signature::from_slice(&sig_bytes).map_err(|_| {
            Error::from(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid Schnorr signature in UnCommittedMetadata",
            ))
        })?;

        Ok(UnCommittedMetadata {
            extra_nonce_1,
            extra_nonce_2,
            broadcast_timestamp,
            signature,
        })
    }
}
