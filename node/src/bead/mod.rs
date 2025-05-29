use crate::committed_metadata::CommittedMetadata;
use crate::uncommitted_metadata::UnCommittedMetadata;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::Error;
use bitcoin::io::{self, BufRead, Write};
use bitcoin::BlockHeader;

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

#[cfg(test)]
mod tests;
