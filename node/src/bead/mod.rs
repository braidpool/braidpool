use crate::committed_metadata::CommittedMetadata;
use crate::uncommitted_metadata::UnCommittedMetadata;
use crate::utils::BeadHash;
use async_trait::async_trait;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::Error;
use bitcoin::io::{self, BufRead, Write};
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, TxMerkleNode};
use libp2p::futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::request_response::Codec;
use libp2p::StreamProtocol;
use serde::{Deserialize, Serialize};
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Bead {
    pub block_header: BlockHeader,
    pub committed_metadata: CommittedMetadata,
    pub uncommitted_metadata: UnCommittedMetadata,
}
impl Default for Bead {
    fn default() -> Self {
        let empty_merkle_bytes: [u8; 32] = [0; 32];
        Self {
            block_header: BlockHeader {
                bits: CompactTarget::from_consensus(486604799),
                merkle_root: TxMerkleNode::from_byte_array(empty_merkle_bytes),
                nonce: 0,
                prev_blockhash: BlockHash::GENESIS_PREVIOUS_BLOCK_HASH,
                time: BlockTime::from_u32(23021),
                version: BlockVersion::TWO,
            },
            committed_metadata: CommittedMetadata::default(),
            uncommitted_metadata: UnCommittedMetadata::default(),
        }
    }
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

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum BeadRequestType {
    GetBeads = 0,
    GetTips = 1,
    GetGenesis = 2,
    GetAllBeads = 3,
    GetBeadsAfter = 4,
    BeadResponseError = 5,
}
//Converting from u8 to `RequestType`/ `ResponseType`
impl BeadRequestType {
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::GetBeads),
            1 => Some(Self::GetTips),
            2 => Some(Self::GetGenesis),
            3 => Some(Self::GetAllBeads),
            4 => Some(Self::GetBeadsAfter),
            5 => Some(Self::BeadResponseError),
            _ => None,
        }
    }
}

// Request types for bead download
#[derive(Debug, Clone, PartialEq)]
pub enum BeadRequest {
    // Request beads from a specific set of hashes
    GetBeads(Vec<BeadHash>),
    // Request the latest tips from a peer
    GetTips,
    GetGenesis,
    GetAllBeads,
    GetBeadsAfter(Vec<BeadHash>),
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
    // Get beads after a specific set of hashes
    GetBeadsAfter(Vec<BeadHash>),
    // Error response
    Error(BeadSyncError),
}

#[derive(Debug, Clone, PartialEq)]
pub enum BeadSyncError {
    GenesisMismatch,
    Other(String),
}

impl Encodable for BeadSyncError {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        match self {
            BeadSyncError::GenesisMismatch => 0u8.consensus_encode(w),
            BeadSyncError::Other(message) => {
                let mut written = 0;
                written += 1u8.consensus_encode(w)?;
                written += message.consensus_encode(w)?;
                Ok(written)
            }
        }
    }
}

impl Decodable for BeadSyncError {
    fn consensus_decode<D: BufRead + ?Sized>(d: &mut D) -> Result<Self, Error> {
        let error_type = u8::consensus_decode(d)?;
        match error_type {
            0 => Ok(BeadSyncError::GenesisMismatch),
            1 => {
                let message = String::consensus_decode(d)?;
                Ok(BeadSyncError::Other(message))
            }
            _ => Err(Error::from(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid BeadSyncError type",
            ))),
        }
    }
}

impl Encodable for BeadRequest {
    fn consensus_encode<W: Write + ?Sized>(&self, writer: &mut W) -> Result<usize, io::Error> {
        match self {
            BeadRequest::GetBeads(hashes) => {
                let mut written = 0;
                written += (BeadRequestType::GetBeads as u8).consensus_encode(writer)?;
                written += (hashes.len() as u32).consensus_encode(writer)?;
                for hash in hashes {
                    written += hash.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadRequest::GetTips => (BeadRequestType::GetTips as u8).consensus_encode(writer),
            BeadRequest::GetGenesis => (BeadRequestType::GetGenesis as u8).consensus_encode(writer),
            BeadRequest::GetAllBeads => {
                (BeadRequestType::GetAllBeads as u8).consensus_encode(writer)
            }
            BeadRequest::GetBeadsAfter(hashes) => {
                let mut written = 0;
                written += (BeadRequestType::GetBeadsAfter as u8).consensus_encode(writer)?;
                written += (hashes.len() as u32).consensus_encode(writer)?;
                for hash in hashes {
                    written += hash.consensus_encode(writer)?;
                }
                Ok(written)
            }
        }
    }
}

impl Decodable for BeadRequest {
    fn consensus_decode<D: BufRead + ?Sized>(d: &mut D) -> Result<Self, Error> {
        let request_type_u8 = u8::consensus_decode(d)?;
        let request_type = BeadRequestType::from_u8(request_type_u8).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "Invalid bead request type")
        })?;
        match request_type {
            BeadRequestType::GetBeads => {
                let count = u32::consensus_decode(d)?;
                let mut hashes = Vec::new();
                for _ in 0..count {
                    let hash = BeadHash::consensus_decode(d)?;
                    hashes.push(hash);
                }
                Ok(BeadRequest::GetBeads(hashes))
            }
            BeadRequestType::GetTips => Ok(BeadRequest::GetTips),
            BeadRequestType::GetGenesis => Ok(BeadRequest::GetGenesis),
            BeadRequestType::GetAllBeads => Ok(BeadRequest::GetAllBeads),
            BeadRequestType::GetBeadsAfter => {
                let count = u32::consensus_decode(d)?;
                let mut hashes = Vec::new();
                for _ in 0..count {
                    let hash = BeadHash::consensus_decode(d)?;
                    hashes.push(hash);
                }
                Ok(BeadRequest::GetBeadsAfter(hashes))
            }
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
                written += (BeadRequestType::GetBeads as u8).consensus_encode(writer)?;
                written += (beads.len() as u32).consensus_encode(writer)?;
                for bead in beads {
                    written += bead.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::Tips(tips) => {
                let mut written = 0;
                written += (BeadRequestType::GetTips as u8).consensus_encode(writer)?;
                written += (tips.len() as u32).consensus_encode(writer)?;
                for tip in tips {
                    written += tip.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::Genesis(genesis) => {
                let mut written = 0;
                written += (BeadRequestType::GetGenesis as u8).consensus_encode(writer)?;
                written += (genesis.len() as u32).consensus_encode(writer)?;
                for hash in genesis {
                    written += hash.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::GetAllBeads(beads) => {
                let mut written = 0;
                written += (BeadRequestType::GetAllBeads as u8).consensus_encode(writer)?;
                written += (beads.len() as u32).consensus_encode(writer)?;
                for bead in beads {
                    written += bead.consensus_encode(writer)?;
                }
                Ok(written)
            }
            BeadResponse::Error(error) => {
                let mut written = 0;
                written += (BeadRequestType::BeadResponseError as u8).consensus_encode(writer)?;
                written += error.consensus_encode(writer)?;
                Ok(written)
            }
            BeadResponse::GetBeadsAfter(beads) => {
                let mut written = 0;
                written += (BeadRequestType::GetBeadsAfter as u8).consensus_encode(writer)?;
                written += (beads.len() as u32).consensus_encode(writer)?;
                for bead_hash in beads {
                    written += bead_hash.consensus_encode(writer)?;
                }
                Ok(written)
            }
        }
    }
}

impl Decodable for BeadResponse {
    fn consensus_decode<D: BufRead + ?Sized>(d: &mut D) -> Result<Self, Error> {
        let response_type_u8 = u8::consensus_decode(d)?;
        let response_type = BeadRequestType::from_u8(response_type_u8).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "Invalid bead response type")
        })?;
        match response_type {
            BeadRequestType::GetBeads => {
                let count = u32::consensus_decode(d)?;
                let mut beads = Vec::new();
                for _ in 0..count {
                    let bead = Bead::consensus_decode(d)?;
                    beads.push(bead);
                }
                Ok(BeadResponse::Beads(beads))
            }
            BeadRequestType::GetTips => {
                let count = u32::consensus_decode(d)?;
                let mut tips = Vec::new();
                for _ in 0..count {
                    let tip = BeadHash::consensus_decode(d)?;
                    tips.push(tip);
                }
                Ok(BeadResponse::Tips(tips))
            }
            BeadRequestType::GetGenesis => {
                let count = u32::consensus_decode(d)?;
                let mut genesis = Vec::new();
                for _ in 0..count {
                    let hash = BeadHash::consensus_decode(d)?;
                    genesis.push(hash);
                }
                Ok(BeadResponse::Genesis(genesis))
            }
            BeadRequestType::GetAllBeads => {
                let count = u32::consensus_decode(d)?;
                let mut beads = Vec::new();
                for _ in 0..count {
                    let bead = Bead::consensus_decode(d)?;
                    beads.push(bead);
                }
                Ok(BeadResponse::GetAllBeads(beads))
            }
            BeadRequestType::BeadResponseError => {
                let error = BeadSyncError::consensus_decode(d)?;
                Ok(BeadResponse::Error(error))
            }
            BeadRequestType::GetBeadsAfter => {
                let count = u32::consensus_decode(d)?;
                let mut bead_hashes = Vec::new();
                for _ in 0..count {
                    let bead_hash = BeadHash::consensus_decode(d)?;
                    bead_hashes.push(bead_hash);
                }
                Ok(BeadResponse::GetBeadsAfter(bead_hashes))
            }
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
