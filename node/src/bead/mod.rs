use crate::braid::Braid;
use crate::committed_metadata::CommittedMetadata;
use crate::uncommitted_metadata::UnCommittedMetadata;
use crate::utils::{BeadLoadError, Parents};
use bitcoin::BlockHash;
use bitcoin::BlockHeader;
use bitcoin::consensus::Error;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::io::{self, BufRead, Write};

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

impl Bead {
    pub fn is_valid_bead(&self) -> bool {
        // Check whether the transactions are included in the block
        true
    }

    pub fn is_genesis_bead(&self, braid: &Braid) -> bool {
        if self.committed_metadata.parents.is_empty() {
            return true;
        };

        // We need to check whether even one of the parent beads have been pruned from memory!
        for parent_bead_hash in self.committed_metadata.parents.iter() {
            let parent_bead = braid.load_bead_from_hash(*parent_bead_hash);
            if let Err(error_type) = parent_bead {
                match error_type {
                    BeadLoadError::BeadPruned => return true,
                    _ => panic!("Fatal Error Detected!"),
                };
            }
        }

        false
    }

    #[inline]
    pub fn is_orphaned(&self, braid: &Braid) -> bool {
        for parent in self.committed_metadata.parents.iter() {
            if braid.beads.contains(parent) == false {
                return true;
            }
        }

        false
    }

    #[inline]
    pub fn get_parents(&self) -> Parents {
        // The bead might get pruned later, so we can't give a shared reference!
        self.committed_metadata.parents.clone()
    }
}

impl Bead {
    pub fn get_bead_hash(&self) -> BlockHash {
        self.block_header.block_hash()
    }
}

impl Bead {
    // All private function definitions go here
    //TODO : To implement a reverse mapping since we will be including the
    //consensus determining attribute in the committed portion and those which
    //will be used afterward such as in retargeting algorithms such as the parentbead_timestamps they shall be
    //included inside the uncommitted portion but the order must be same as that of the hashset of parents_bead_hashes present
    //inside the committed metadata
}

#[cfg(test)]
mod tests;
