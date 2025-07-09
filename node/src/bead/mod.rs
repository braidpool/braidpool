use crate::committed_metadata::CommittedMetadata;
use crate::uncommitted_metadata::UnCommittedMetadata;
use crate::utils::{hashset_to_vec_deterministic, BeadHash};
use async_trait::async_trait;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::Error;
use bitcoin::io::{self, BufRead, Write};
use bitcoin::BlockHeader;
use libp2p::futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::request_response::Codec;
use libp2p::StreamProtocol;
use std::collections::HashSet;

const GET_BEADS: u8 = 0;
const GET_TIPS: u8 = 1;
const GET_GENESIS: u8 = 2;
const GET_ALL_BEADS: u8 = 3;
const BEAD_RESPONSE_ERROR: u8 = 4;

#[derive(Clone, Debug, PartialEq)]
pub struct Bead {
    pub block_header: BlockHeader,
    pub committed_metadata: CommittedMetadata,
    pub uncommitted_metadata: UnCommittedMetadata,
}

impl Encodable for Bead {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.block_header.consensus_encode(w)?;
        len += self.committed_metadata.consensus_encode(w)?;
        len += self.uncommitted_metadata.consensus_encode(w)?;
        Ok(len)
    }
}

impl Decodable for Bead {
    fn consensus_decode<R: BufRead + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let block_header = BlockHeader::consensus_decode(r)?;
        let committed_metadata = CommittedMetadata::consensus_decode(r)?;
        let uncommitted_metadata = UnCommittedMetadata::consensus_decode(r)?;
        Ok(Bead {
            block_header,
            committed_metadata,
            uncommitted_metadata,
        })
    }
}

// Request types for bead download
#[derive(Debug, Clone, PartialEq)]
pub enum BeadRequest {
    // Request beads from a specific set of hashes
    GetBeads(HashSet<BeadHash>),
    // Request the latest tips from a peer
    GetTips,
    GetGenesis,
    GetAllBeads,
}

// Response types for bead download
#[derive(Debug, Clone, PartialEq)]
pub enum BeadResponse {
    // Response containing requested beads
    Beads(Vec<Bead>),
    // Response containing tips
    Tips(Vec<BeadHash>),
    // Response containing genesis
    Genesis(Vec<BeadHash>),
    // Get all beads for IBD
    GetAllBeads(Vec<Bead>),
    // Error response
    Error(String),
}

impl Encodable for BeadRequest {
    fn consensus_encode<W: Write + ?Sized>(&self, writer: &mut W) -> Result<usize, io::Error> {
        match self {
            BeadRequest::GetBeads(hashes) => {
                let mut written = 0;
                written += GET_BEADS.consensus_encode(writer)?; // 0 for GetBeads
                let hashes_vec = hashset_to_vec_deterministic(hashes);
                written += (hashes_vec.len() as u32).consensus_encode(writer)?;
                for hash in hashes_vec {
                    written += hash.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadRequest::GetTips => {
                GET_TIPS.consensus_encode(writer) // 1 for GetTips
            }
            BeadRequest::GetGenesis => {
                GET_GENESIS.consensus_encode(writer) // 2 for GetGenesis
            }
            BeadRequest::GetAllBeads => {
                GET_ALL_BEADS.consensus_encode(writer) // 3 for GetAllBeads
            }
        }
    }
}

impl Decodable for BeadRequest {
    fn consensus_decode<D: BufRead + ?Sized>(d: &mut D) -> Result<Self, Error> {
        let request_type = u8::consensus_decode(d)?;
        match request_type {
            GET_BEADS => {
                let count = u32::consensus_decode(d)?;
                let mut hashes = HashSet::new();
                for _ in 0..count {
                    let hash = BeadHash::consensus_decode(d)?;
                    hashes.insert(hash);
                }
                Ok(BeadRequest::GetBeads(hashes))
            }
            GET_TIPS => Ok(BeadRequest::GetTips),
            GET_GENESIS => Ok(BeadRequest::GetGenesis),
            GET_ALL_BEADS => Ok(BeadRequest::GetAllBeads),
            _ => Err(Error::from(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid BeadRequest type",
            ))),
        }
    }
}

impl Encodable for BeadResponse {
    fn consensus_encode<W: Write + ?Sized>(&self, writer: &mut W) -> Result<usize, io::Error> {
        match self {
            BeadResponse::Beads(beads) => {
                let mut written = 0;
                written += GET_BEADS.consensus_encode(writer)?; // 0 for Beads
                written += (beads.len() as u32).consensus_encode(writer)?;
                for bead in beads {
                    written += bead.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::Tips(tips) => {
                let mut written = 0;
                written += GET_TIPS.consensus_encode(writer)?; // 1 for Tips
                written += (tips.len() as u32).consensus_encode(writer)?;
                for tip in tips {
                    written += tip.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::Genesis(genesis) => {
                let mut written = 0;
                written += GET_GENESIS.consensus_encode(writer)?; // 2 for Genesis
                written += (genesis.len() as u32).consensus_encode(writer)?;
                for hash in genesis {
                    written += hash.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::GetAllBeads(beads) => {
                let mut written = 0;
                written += GET_ALL_BEADS.consensus_encode(writer)?; // 3 for GetAllBeads
                written += (beads.len() as u32).consensus_encode(writer)?;
                for bead in beads {
                    written += bead.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::Error(error) => {
                let mut written = 0;
                written += BEAD_RESPONSE_ERROR.consensus_encode(writer)?; // 4 for Error
                written += error.consensus_encode(writer)?;
                Ok(written)
            }
        }
    }
}

impl Decodable for BeadResponse {
    fn consensus_decode<D: BufRead + ?Sized>(d: &mut D) -> Result<Self, Error> {
        let response_type = u8::consensus_decode(d)?;
        match response_type {
            GET_BEADS => {
                let count = u32::consensus_decode(d)?;
                let mut beads = Vec::new();
                for _ in 0..count {
                    let bead = Bead::consensus_decode(d)?;
                    beads.push(bead);
                }
                Ok(BeadResponse::Beads(beads))
            }
            GET_TIPS => {
                let count = u32::consensus_decode(d)?;
                let mut tips = Vec::new();
                for _ in 0..count {
                    let tip = BeadHash::consensus_decode(d)?;
                    tips.push(tip);
                }
                Ok(BeadResponse::Tips(tips))
            }
            GET_GENESIS => {
                let count = u32::consensus_decode(d)?;
                let mut genesis = Vec::new();
                for _ in 0..count {
                    let hash = BeadHash::consensus_decode(d)?;
                    genesis.push(hash);
                }
                Ok(BeadResponse::Genesis(genesis))
            }
            GET_ALL_BEADS => {
                let count = u32::consensus_decode(d)?;
                let mut beads = Vec::new();
                for _ in 0..count {
                    let bead = Bead::consensus_decode(d)?;
                    beads.push(bead);
                }
                Ok(BeadResponse::GetAllBeads(beads))
            }
            BEAD_RESPONSE_ERROR => {
                let error = String::consensus_decode(d)?;
                Ok(BeadResponse::Error(error))
            }
            _ => Err(Error::from(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid BeadResponse type",
            ))),
        }
    }
}

#[derive(Clone, Default)]
pub struct BeadCodec;

#[async_trait]
impl Codec for BeadCodec {
    type Protocol = StreamProtocol;
    type Request = BeadRequest;
    type Response = BeadResponse;

    async fn read_request<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
    ) -> std::io::Result<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut buf = Vec::new();
        io.read_to_end(&mut buf).await?;
        BeadRequest::consensus_decode(&mut buf.as_slice())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    async fn read_response<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
    ) -> std::io::Result<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let mut buf = Vec::new();
        io.read_to_end(&mut buf).await?;
        BeadResponse::consensus_decode(&mut buf.as_slice())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    async fn write_request<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        request: Self::Request,
    ) -> std::io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        let mut buf = Vec::new();
        request
            .consensus_encode(&mut buf)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        io.write_all(&buf)
            .await
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
    }

    async fn write_response<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        response: Self::Response,
    ) -> std::io::Result<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        let mut buf = Vec::new();
        response
            .consensus_encode(&mut buf)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        io.write_all(&buf)
            .await
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
    }
}

#[cfg(test)]
mod tests;
