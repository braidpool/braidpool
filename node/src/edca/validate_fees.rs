use crate::bead::Bead;
use crate::config::PoolNetwork;
use crate::edca::cmempool_state::StateKey;
use crate::error::FeeProofError;
use bitcoin::hashes::{sha256d, Hash, HashEngine};
use bitcoin::{Amount, BlockHash, Network, TxMerkleNode, Txid};
use std::collections::BTreeMap;

/// Block subsidy at height zero or genesis block in satoshis .
const INITIAL_SUBSIDY_SATS: u64 = 5_000_000_000;

/// Returns the number of blocks between subsidy halvings on `network`.
pub fn subsidy_halving_interval(network: PoolNetwork) -> u64 {
    match network {
        PoolNetwork::Bitcoin(Network::Regtest) => 150,
        PoolNetwork::Cpunet | PoolNetwork::Bitcoin(_) => 210_000,
    }
}

/// Returns the block subsidy at `height` on `network`, in satoshis.
pub fn block_subsidy_sats(height: u64, network: PoolNetwork) -> u64 {
    let halvings = height / subsidy_halving_interval(network);
    if halvings >= 64 {
        return 0;
    }
    INITIAL_SUBSIDY_SATS >> halvings
}

/// The fee claim of a bead, verified against the template it was mined on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FeeCommitment {
    /// Height of the block the template builds.
    pub height: u64,
    /// The block subsidy at `height`, in satoshis.
    pub subsidy_sats: u64,
    /// The most a coinbase on the template may pay, in satoshis:
    /// `subsidy_sats + fee_total_sats`.
    pub coinbase_value_sats: u64,
    /// The verified fee total `F_i`, in satoshis.
    pub fee_total_sats: u64,
}

/// Identifies a template by the merkle branch above its coinbase.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BranchKey([u8; 32]);

impl BranchKey {
    /// Derives the key from a coinbase merkle branch.
    pub fn from_branch(branch: &[[u8; 32]]) -> Self {
        let mut engine = sha256d::Hash::engine();
        for sibling in branch {
            engine.input(sibling);
        }
        BranchKey(sha256d::Hash::from_engine(engine).to_byte_array())
    }

    /// Returns the raw digest.
    pub fn to_byte_array(self) -> [u8; 32] {
        self.0
    }
}

/// Hashes two merkle nodes into their parent.
fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut engine = sha256d::Hash::engine();
    engine.input(left);
    engine.input(right);
    sha256d::Hash::from_engine(engine).to_byte_array()
}

/// Folds a coinbase txid up a merkle branch into the root it implies.
pub fn root_from_branch(coinbase_txid: Txid, branch: &[[u8; 32]]) -> TxMerkleNode {
    let mut current = coinbase_txid.to_byte_array();
    for sibling in branch {
        current = hash_pair(&current, sibling);
    }
    TxMerkleNode::from_byte_array(current)
}

/// Where a committed-mempool state sits on the Bitcoin chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChainAnchor {
    /// Block the state builds on.
    pub prev_blockhash: BlockHash,
    /// Height of the block being built, one past `prev_blockhash`.
    pub height: u64,
    /// Block subsidy at `height`, in satoshis.
    pub subsidy_sats: u64,
}

impl ChainAnchor {
    /// Anchors a state to `prev_blockhash` at `height` on `network`.
    pub fn new(prev_blockhash: BlockHash, height: u64, network: PoolNetwork) -> Self {
        Self {
            prev_blockhash,
            height,
            subsidy_sats: block_subsidy_sats(height, network),
        }
    }
}

/// A template this node issued, priced once when it was built.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemplateEntry {
    /// Chain position this template builds on.
    pub anchor: ChainAnchor,
    /// Identifies the committed-mempool state the template was built from.
    pub state_key: StateKey,
    /// Identifies the template by its branch.
    pub key: BranchKey,
    /// Merkle siblings above the coinbase, shared by every bead mined on it.
    pub coinbase_branch: Vec<[u8; 32]>,
    /// `F_i` for every bead mined on this template, in satoshis.
    pub fee_total_sats: u64,
    /// Transactions in the template, coinbase excluded.
    pub tx_count: usize,
}

impl TemplateEntry {
    /// Prices a template from the branch and fees Bitcoin Core returned.
    ///
    /// `state_key` names the transaction set the template holds, coinbase
    /// excluded, and `fees_sats` carries one fee per such transaction.
    pub fn new(
        anchor: ChainAnchor,
        state_key: StateKey,
        coinbase_branch: Vec<[u8; 32]>,
        fees_sats: &[u64],
    ) -> Result<Self, FeeProofError> {
        let fee_total_sats = fees_sats
            .iter()
            .try_fold(0u64, |total, fee| total.checked_add(*fee))
            .filter(|total| *total <= Amount::MAX_MONEY.to_sat())
            .ok_or(FeeProofError::FeeTotalOverflow)?;

        Ok(Self {
            anchor,
            state_key,
            key: BranchKey::from_branch(&coinbase_branch),
            coinbase_branch,
            fee_total_sats,
            tx_count: fees_sats.len(),
        })
    }
    /// Prices a template whose merkle branch arrives as raw byte vectors.
    pub fn from_branch_bytes(
        anchor: ChainAnchor,
        state_key: StateKey,
        coinbase_merkle_path: &[Vec<u8>],
        fees_sats: &[u64],
    ) -> Result<Self, FeeProofError> {
        let mut branch: Vec<[u8; 32]> = Vec::with_capacity(coinbase_merkle_path.len());
        for sibling in coinbase_merkle_path {
            let bytes: [u8; 32] =
                sibling
                    .as_slice()
                    .try_into()
                    .map_err(|_| FeeProofError::InvalidMerkleBranch {
                        length: sibling.len(),
                    })?;
            branch.push(bytes);
        }
        Self::new(anchor, state_key, branch, fees_sats)
    }

    /// Returns whether a bead's header commits to this template.
    pub fn matches(&self, coinbase_txid: Txid, header_root: TxMerkleNode) -> bool {
        root_from_branch(coinbase_txid, &self.coinbase_branch) == header_root
    }

    /// Returns what a coinbase on this template may pay, in satoshis.
    ///
    /// `None` only if subsidy plus fees leaves the money range.
    pub fn coinbase_value_sats(&self) -> Option<u64> {
        self.anchor.subsidy_sats.checked_add(self.fee_total_sats)
    }
}

/// Checks a bead against the template it should have mined.
pub fn verify_fee_against_template(
    bead: &Bead,
    coinbase_txid: Txid,
    template: &TemplateEntry,
) -> Result<FeeCommitment, FeeProofError> {
    if bead.block_header.prev_blockhash != template.anchor.prev_blockhash {
        return Err(FeeProofError::AnchorMismatch {
            expected: template.anchor.prev_blockhash,
            found: bead.block_header.prev_blockhash,
        });
    }

    let computed = root_from_branch(coinbase_txid, &template.coinbase_branch);
    if computed != bead.block_header.merkle_root {
        return Err(FeeProofError::MerkleRootMismatch {
            header: bead.block_header.merkle_root,
            computed,
        });
    }

    let claimed_fee_sats = bead.committed_metadata.fee_total_sats;
    if claimed_fee_sats != template.fee_total_sats {
        return Err(FeeProofError::FeeCommitmentMismatch {
            claimed_fee_sats,
            derived_fee_sats: template.fee_total_sats,
        });
    }

    let coinbase_value_sats = template
        .coinbase_value_sats()
        .ok_or(FeeProofError::CoinbaseValueOverflow)?;

    Ok(FeeCommitment {
        height: template.anchor.height,
        subsidy_sats: template.anchor.subsidy_sats,
        coinbase_value_sats,
        fee_total_sats: template.fee_total_sats,
    })
}

/// What a node concluded about a bead's fee total.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FeeVerdict {
    /// The bead built on a template this node priced, and its committed total
    /// agrees with it.
    Verified {
        /// `F_i` for this bead, in satoshis.
        fee_sats: u64,
    },
    /// The bead built on a known template but committed a different total, so
    /// the claim is false.
    Deviated,
    /// No known template explains this bead; it may be honest but built on a
    /// set this node never held.
    Unknown,
}

/// Supplies fee verdicts for beads.
pub trait FeeVerdictSource {
    /// Returns what this node concluded about `bead`'s fee total.
    fn verdict(&self, bead: &Bead) -> FeeVerdict;
}

/// Most template snapshots retained at once.
pub const MAX_CACHED_SNAPSHOTS: usize = 4096;

/// Templates this node issued, looked up by the committed-mempool state they
/// were built from.
#[derive(Debug, Clone, Default)]
pub struct TemplateCache {
    /// Snapshots keyed by chain position and state, each tagged with the order
    /// it was inserted in.
    templates: BTreeMap<(BlockHash, StateKey), (u64, TemplateEntry)>,
    /// Insertion counter, so the oldest snapshot can be evicted.
    next_sequence: u64,
}

impl TemplateCache {
    /// Creates an empty cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// Records a template this node issued, replacing any earlier template
    /// built from the same state on the same block.
    pub fn insert(&mut self, template: TemplateEntry) {
        let sequence = self.next_sequence;
        self.next_sequence += 1;
        self.templates.insert(
            (template.anchor.prev_blockhash, template.state_key),
            (sequence, template),
        );
        while self.templates.len() > MAX_CACHED_SNAPSHOTS {
            let oldest = self
                .templates
                .iter()
                .min_by_key(|(_, (sequence, _))| *sequence)
                .map(|(key, _)| *key);
            match oldest {
                Some(key) => self.templates.remove(&key),
                None => break,
            };
        }
    }

    /// Returns the template built on `prev_blockhash` from the state
    /// `state_key`, if retained.
    pub fn get(&self, prev_blockhash: BlockHash, state_key: StateKey) -> Option<&TemplateEntry> {
        self.templates
            .get(&(prev_blockhash, state_key))
            .map(|(_, template)| template)
    }

    /// Drops every template that does not build on `prev_blockhash`.
    pub fn retain_block(&mut self, prev_blockhash: BlockHash) {
        self.templates
            .retain(|(block, _), _| *block == prev_blockhash);
    }

    /// Returns how many templates are retained.
    pub fn len(&self) -> usize {
        self.templates.len()
    }

    /// Returns whether no template is retained.
    pub fn is_empty(&self) -> bool {
        self.templates.is_empty()
    }
}
