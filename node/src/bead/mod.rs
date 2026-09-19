use crate::committed_metadata::CommittedMetadata;
use crate::ibd_manager::IBD_BATCH_SIZE;
use crate::uncommitted_metadata::UnCommittedMetadata;
use crate::utils::BeadHash;
use async_trait::async_trait;
use bitcoin::block::Header as BlockHeader;
use bitcoin::block::Version as BlockVersion;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::encode::MAX_VEC_SIZE;
use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, CompactTarget, TxMerkleNode};
use libp2p::futures::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use libp2p::request_response::Codec;
use libp2p::StreamProtocol;
use serde::{Deserialize, Serialize};
use std::io::{Error as IoError, ErrorKind, Result as IoResult};

/// Collection of beads.
///
/// Newtype wrapper around `Vec<Bead>` that provides Bitcoin consensus encoding/decoding
/// and convenient iteration methods. Used to work around Rust's orphan rule.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Beads(pub Vec<Bead>);
impl_vec_wrapper!(Beads, Bead);

/// Collection of bead hashes.
///
/// Newtype wrapper around `Vec<BeadHash>` that provides Bitcoin consensus encoding/decoding
/// and convenient iteration methods. Used for requesting and responding with bead identifiers.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct BeadHashes(pub Vec<BeadHash>);
impl_vec_wrapper!(BeadHashes, BeadHash);

/// A bead in the Braidpool DAG structure.
///
/// A bead represents a weak share in the Braidpool mining protocol. It combines a Bitcoin
/// block header with metadata about the mining process and network topology.
///
/// **Fields:**
/// - `block_header`: Standard Bitcoin block header with proof-of-work
/// - `committed_metadata`: Metadata committed to the block (parents, timestamps, transactions)
/// - `uncommitted_metadata`: Metadata not part of the hash (signature, broadcast time)
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Bead {
    pub block_header: BlockHeader,
    pub committed_metadata: CommittedMetadata,
    pub uncommitted_metadata: UnCommittedMetadata,
}
impl_consensus_encoding!(Bead, block_header, committed_metadata, uncommitted_metadata);

impl Default for Bead {
    fn default() -> Self {
        let empty_merkle_bytes: [u8; 32] = [0; 32];
        Self {
            block_header: BlockHeader {
                bits: CompactTarget::from_consensus(1),
                merkle_root: TxMerkleNode::from_byte_array(empty_merkle_bytes),
                nonce: 0,
                prev_blockhash: BlockHash::all_zeros(),
                time: 0,
                version: BlockVersion::TWO,
            },
            committed_metadata: CommittedMetadata::default(),
            uncommitted_metadata: UnCommittedMetadata::default(),
        }
    }
}

braidpool_protocol! {
    /// Request types for bead synchronization protocol.
    ///
    /// Used in the request-response protocol to request beads from remote peers.
    /// Each variant maps to a specific opcode for network encoding.
    ///
    /// **Variants:**
    /// - `GetBeads(BeadHashes)`: Request specific beads by their hashes
    /// - `GetTips`: Request the current DAG tips
    /// - `GetGenesis`: Request the genesis bead(s)
    /// - `GetAllBeads`: Request all beads (for IBD)
    /// - `GetBeadsAfter(BeadHashes)`: Request all beads after specified hashes (for sync)
    pub enum BeadRequest {
        GetBeads(BeadHashes)        = 0,
        GetTips                     = 1,
        GetGenesis                  = 2,
        GetAllBeads                 = 3,
        GetBeadsAfter(BeadHashes)   = 4,
    }
}

braidpool_protocol! {
    /// Response types for bead synchronization protocol.
    ///
    /// Responses to `BeadRequest` messages. Contains either the requested data
    /// or an error explaining why the request couldn't be fulfilled.
    ///
    /// **Variants:**
    /// - `Beads(Beads)`: Response containing requested beads
    /// - `Tips(BeadHashes)`: Response containing current DAG tip hashes
    /// - `Genesis(BeadHashes)`: Response containing genesis bead hash(es)
    /// - `GetAllBeads(Beads)`: Response containing all beads (for IBD)
    /// - `GetBeadsAfter(BeadHashes)`: Response containing beads after specified hashes
    /// - `Error(BeadSyncError)`: Error response indicating why request failed
    pub enum BeadResponse {
        Beads(Beads)                = 0,
        Tips(BeadHashes)            = 1,
        Genesis(BeadHashes)         = 2,
        GetAllBeads(Beads)          = 3,
        GetBeadsAfter(BeadHashes)   = 4,
        Error(BeadSyncError)        = 5,
    }
}

braidpool_protocol! {
    /// Errors that can occur during bead synchronization.
    ///
    /// These errors are returned in `BeadResponse::Error` to indicate
    /// why a bead request could not be fulfilled.
    ///
    /// **Variants:**
    /// - `GenesisMismatch`: Genesis beads don't match between peers
    /// - `BeadHashNotFound`: Requested bead hash not found in local store
    pub enum BeadSyncError {
        GenesisMismatch     = 0,
        BeadHashNotFound    = 1,
    }
}

/// Largest bead sync request a peer may send, in bytes.
///
/// Requests carry hash lists. The largest one the client builds is a `GetBeads`
/// of `IBD_BATCH_SIZE` hashes (16 KiB), so 1 MiB leaves ample headroom while
/// bounding what an unsolicited peer can make the node buffer.
pub const MAX_BEAD_SYNC_REQUEST_BYTES: u64 = 1024 * 1024;

/// Largest bead sync response a peer may send, in bytes.
///
/// One IBD batch of beads, each of which the consensus decoder already refuses
/// to read past `MAX_VEC_SIZE`. Derived from those two existing limits so the
/// cap can never reject a response the decoder would have accepted.
pub const MAX_BEAD_SYNC_RESPONSE_BYTES: u64 = IBD_BATCH_SIZE as u64 * MAX_VEC_SIZE as u64;

/// Reads the whole stream into memory, failing if it holds more than `max` bytes.
///
/// Reads `max + 1` so an oversized stream is reported as an error instead of
/// being silently truncated to a prefix that might still decode.
async fn read_bounded<T>(io: &mut T, max: u64) -> IoResult<Vec<u8>>
where
    T: AsyncRead + Unpin + Send,
{
    let mut buf = Vec::new();
    io.take(max + 1).read_to_end(&mut buf).await?;
    if buf.len() as u64 > max {
        return Err(IoError::new(
            ErrorKind::InvalidData,
            format!("bead sync message exceeds {max} bytes"),
        ));
    }
    Ok(buf)
}

/// Codec for encoding/decoding bead sync messages over libp2p.
///
/// Implements the `libp2p::request_response::Codec` trait to handle serialization
/// of `BeadRequest` and `BeadResponse` messages using Bitcoin consensus encoding.
#[derive(Clone, Default)]
pub struct BeadCodec;

#[async_trait]
impl Codec for BeadCodec {
    type Protocol = StreamProtocol;
    type Request = BeadRequest;
    type Response = BeadResponse;

    async fn read_request<T>(&mut self, _: &Self::Protocol, io: &mut T) -> IoResult<Self::Request>
    where
        T: AsyncRead + Unpin + Send,
    {
        let buf = read_bounded(io, MAX_BEAD_SYNC_REQUEST_BYTES).await?;
        BeadRequest::consensus_decode(&mut buf.as_slice())
            .map_err(|e| IoError::new(ErrorKind::InvalidData, e))
    }

    async fn read_response<T>(&mut self, _: &Self::Protocol, io: &mut T) -> IoResult<Self::Response>
    where
        T: AsyncRead + Unpin + Send,
    {
        let buf = read_bounded(io, MAX_BEAD_SYNC_RESPONSE_BYTES).await?;
        BeadResponse::consensus_decode(&mut buf.as_slice())
            .map_err(|e| IoError::new(ErrorKind::InvalidData, e))
    }

    async fn write_request<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        request: Self::Request,
    ) -> IoResult<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        let mut buf = Vec::new();
        request
            .consensus_encode(&mut buf)
            .map_err(|e| IoError::new(ErrorKind::InvalidData, e))?;
        io.write_all(&buf)
            .await
            .map_err(|e| IoError::new(ErrorKind::Other, e))
    }

    async fn write_response<T>(
        &mut self,
        _: &Self::Protocol,
        io: &mut T,
        response: Self::Response,
    ) -> IoResult<()>
    where
        T: AsyncWrite + Unpin + Send,
    {
        let mut buf = Vec::new();
        response
            .consensus_encode(&mut buf)
            .map_err(|e| IoError::new(ErrorKind::InvalidData, e))?;
        io.write_all(&buf)
            .await
            .map_err(|e| IoError::new(ErrorKind::Other, e))
    }
}

#[cfg(test)]
mod tests;
