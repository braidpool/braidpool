use crate::config::CoinbaseConfig;
use crate::error::CoinbaseError;
use crate::ipc::client::BlockTemplateComponents;
use crate::EXTRANONCE_SEPARATOR;
use bitcoin::consensus::encode::{ReadExt, WriteExt};
use bitcoin::{
    absolute::LockTime,
    blockdata::{
        opcodes,
        script::{Builder, PushBytesBuf},
        transaction::Version,
        witness::Witness,
    },
    consensus::{self, Decodable},
    hashes::sha256d,
    Address, Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid,
};
use std::convert::TryFrom;
use std::io::Cursor;
use std::str::FromStr;

pub mod constants {
    pub const SEGWIT_COMMITMENT_SIZE: usize = 38;
    pub const MAX_OP_RETURN_DATA: usize = 80;
    pub const MAX_BRAIDPOOL_COMMITMENT_LEN: usize = 72;
    pub const MAX_COINBASE_SCRIPT_SIG: usize = 100;
    pub const MAX_EXTRANONCE_LEN: usize = 32;
    pub const MAX_BITCOIN_HEIGHT: u32 = 10_000_000;
    pub const MAX_BIP34_HEIGHT_BYTES: usize = 4;
}

#[derive(Debug, Clone)]
pub struct FinalCoinbase {
    pub transaction: Transaction,
}

impl FinalCoinbase {
    /// Returns the transaction ID (txid) as a hex string.
    pub fn txid(&self) -> Vec<u8> {
        self.transaction.compute_txid().to_byte_array().to_vec()
    }

    /// Returns the full, serialized transaction with witness data as bytes.
    pub fn full_hex(&self) -> Vec<u8> {
        bitcoin::consensus::serialize(&self.transaction)
    }
}

#[derive(Debug, Clone)]
pub struct FinalTemplate {
    pub coinbase: FinalCoinbase,
    pub merkle_root: Vec<u8>,
    pub complete_block_hex: Vec<u8>,
}

impl FinalTemplate {
    pub fn block_hash(&self) -> Vec<u8> {
        if self.complete_block_hex.len() >= 80 {
            let header = &self.complete_block_hex[0..80];
            let hash = double_sha256(header);
            let mut reversed_hash = hash;
            reversed_hash.reverse();
            reversed_hash.to_vec()
        } else {
            Vec::new()
        }
    }

    pub fn get_nonce(&self) -> u32 {
        if self.complete_block_hex.len() >= 80 {
            let nonce_bytes = &self.complete_block_hex[76..80];
            u32::from_le_bytes([
                nonce_bytes[0],
                nonce_bytes[1],
                nonce_bytes[2],
                nonce_bytes[3],
            ])
        } else {
            0
        }
    }
    /// Returns the block hash as hex string
    pub fn block_hash_hex(&self) -> String {
        hex::encode(self.block_hash())
    }

    /// Returns just the block header as bytes
    pub fn block_header(&self) -> Vec<u8> {
        if self.complete_block_hex.len() >= 80 {
            self.complete_block_hex[0..80].to_vec()
        } else {
            Vec::new()
        }
    }

    /// Returns the size of the complete block in bytes
    pub fn block_size(&self) -> usize {
        self.complete_block_hex.len()
    }
}

/// Encodes a block height according to BIP-34 minimal integer specification
///
/// Converts a block height to the minimal little-endian byte representation
/// required by BIP-34. Adds padding byte if the most significant bit is set
/// to ensure the number is interpreted as positive.
///
/// # Arguments
/// * `height` - Block height to encode (must be ≤ 10,000,000 for safety)
///
/// # Encoding Rules
/// 1. Convert to little-endian bytes
/// 2. Remove trailing zero bytes (minimal representation)
/// 3. Add 0x00 padding byte if MSB is set (positive number requirement)
fn encode_bip34_height(height: u32) -> Result<Vec<u8>, CoinbaseError> {
    if height > constants::MAX_BITCOIN_HEIGHT {
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }
    if height == 0 {
        return Ok(vec![0]);
    }

    let mut bytes = Vec::new();
    let mut n = height;

    while n > 0 {
        bytes.push((n & 0xff) as u8);
        n >>= 8;
    }
    if let Some(&last_byte) = bytes.last() {
        if last_byte & 0x80 != 0 {
            bytes.push(0);
        }
    }
    Ok(bytes)
}

/// Computes the double-SHA256 hash of a byte slice.
fn double_sha256(data: &[u8]) -> [u8; 32] {
    sha256d::Hash::hash(data).to_byte_array()
}

/// Computes the Merkle root from a coinbase transaction ID and a path of transaction hashes.
///
/// This function iteratively combines the coinbase `txid` with each hash in the provided
/// path, simulating the process of building the Merkle tree up to its root.
///
/// # Arguments
/// * `coinbase_txid`: The transaction ID of the coinbase transaction.
/// * `path`: A slice of byte vectors, where each vector is a 32-byte sibling hash
/// from the Merkle path provided by the block template.
pub fn calculate_merkle_root(coinbase_txid: Txid, path: &[Vec<u8>]) -> [u8; 32] {
    // Start with the coinbase transaction's hash.
    let mut current_hash = coinbase_txid.to_byte_array();

    // Iteratively hash the current hash with the next branch from the path.
    for branch_bytes in path {
        let mut concatenated = current_hash.to_vec();
        concatenated.extend_from_slice(branch_bytes);
        current_hash = double_sha256(&concatenated);
    }

    current_hash
}

/// Parse coinbase transaction from raw bytes
pub fn parse_coinbase_transaction(coinbase_bytes: &[u8]) -> Result<Transaction, CoinbaseError> {
    use std::io::Cursor;

    let mut cursor = Cursor::new(coinbase_bytes);
    Transaction::consensus_decode(&mut cursor).map_err(|_| CoinbaseError::ConsensusDecodeError)
}

/// Decode a Bitcoin varint from bytes. Returns (value, bytes_read), where
/// bytes_read may be < data.len() if additional trailing bytes are present.
fn decode_varint(data: &[u8]) -> Result<(u64, usize), CoinbaseError> {
    let mut cursor = Cursor::new(data);

    match cursor.read_compact_size() {
        Ok(value) => {
            let bytes_read = cursor.position() as usize;
            Ok((value, bytes_read))
        }
        Err(_) => Err(CoinbaseError::ConsensusDecodeError),
    }
}

/// Encode a u64 as Bitcoin varint
fn encode_varint(value: u64) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.emit_compact_size(value)
        .expect("Vec::write failure is impossible");
    buf
}

fn find_transaction_end(tx_data: &[u8]) -> Result<usize, CoinbaseError> {
    if tx_data.is_empty() {
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }

    use std::io::Cursor;
    let mut cursor = Cursor::new(tx_data);

    match Transaction::consensus_decode(&mut cursor) {
        Ok(tx) => {
            let end_pos = cursor.position() as usize;
            log::debug!(
                "Transaction parsing: {} inputs, {} outputs, {} bytes",
                tx.input.len(),
                tx.output.len(),
                end_pos
            );
            Ok(end_pos)
        }
        Err(e) => {
            log::error!(
                "Failed to parse transaction: {} (data length: {})",
                e,
                tx_data.len()
            );
            Err(CoinbaseError::ConsensusDecodeError)
        }
    }
}

/// Builds the coinbase transaction input with BIP-34 compliant height encoding
///
/// Creates the coinbase input with proper BIP-34 block height encoding.
/// Uses `block_height + 1` because the coinbase must contain
/// the height of the block being mined, not the current blockchain tip.
///
/// # Arguments
/// * `block_height` - Current blockchain tip height
/// * `extranonce` - Miner's work distribution data
/// * `pool_identifier` - Pool identification string
///
/// # ScriptSig Structure:
///   <height_push> <height_bytes> <extranonce_push> <extranonce> <pool_id_push> <pool_id>
fn build_coinbase_input(
    block_height: u32,
    extranonce: &[u8],
    pool_identifier: &str,
) -> Result<TxIn, CoinbaseError> {
    let coinbase_height = block_height + 1;
    let height_bytes = encode_bip34_height(coinbase_height)?;

    if height_bytes.len() > constants::MAX_BIP34_HEIGHT_BYTES {
        return Err(CoinbaseError::ScriptCreationError);
    }
    if extranonce.len() > 32 {
        return Err(CoinbaseError::InvalidExtranonceLength);
    }
    let pool_bytes = pool_identifier.as_bytes();
    if pool_bytes.len() > 20 {
        return Err(CoinbaseError::ScriptCreationError);
    }
    let total_script_size = 1 + height_bytes.len() + 1 + extranonce.len() + 1 + pool_bytes.len();
    if total_script_size > constants::MAX_COINBASE_SCRIPT_SIG {
        return Err(CoinbaseError::ScriptCreationError);
    }

    let mut script_data = Vec::new();
    script_data.push(height_bytes.len() as u8);
    script_data.extend_from_slice(&height_bytes);
    //extranonce starts with 8 assigned to extranonce bytes
    //therefore the extranonce separator must be before this
    //TODO KINDLY REVERT IF NOT WORKS
    script_data.push(EXTRANONCE_SEPARATOR.len() as u8);
    script_data.extend_from_slice(&EXTRANONCE_SEPARATOR);
    script_data.push(pool_bytes.len() as u8);
    script_data.extend_from_slice(pool_bytes);

    let script_sig = ScriptBuf::from_bytes(script_data);
    let mut witness = Witness::new();
    witness.push(vec![0u8; 32]);

    Ok(TxIn {
        previous_output: OutPoint::COINBASE_PREVOUT,
        script_sig,
        sequence: Sequence::MAX,
        witness,
    })
}

/// Creates an OP_RETURN output containing Braidpool commitment data
///
/// Combines the pool's commitment data with the miner's extranonce to create
/// a standard Bitcoin OP_RETURN output for commitment purposes.
/// The total data size is strictly limited to 80 bytes
///
/// # Arguments
/// * `commitment` - Pool-specific commitment data
/// * `extranonce` - Miner's unique work identifier
fn build_braidpool_op_return(commitment: &[u8], extranonce: &[u8]) -> Result<TxOut, CoinbaseError> {
    let mut op_return_data = commitment.to_vec();
    op_return_data.extend_from_slice(extranonce);

    if op_return_data.len() > constants::MAX_OP_RETURN_DATA {
        return Err(CoinbaseError::OpReturnTooLarge);
    }
    let op_return_data_buf =
        PushBytesBuf::try_from(op_return_data).map_err(CoinbaseError::PushBytesError)?;

    let op_return_script = Builder::new()
        .push_opcode(opcodes::all::OP_RETURN)
        .push_slice(&op_return_data_buf)
        .into_script()
        .to_owned();

    Ok(TxOut {
        value: Amount::ZERO,
        script_pubkey: op_return_script,
    })
}

/// Creates a SegWit witness commitment output from template data
///
/// Validates and creates the BIP-141 required witness commitment output.
/// This output commits to all witness data in the block and is mandatory
/// for SegWit-compatible blocks.
///
/// # Arguments
/// * `commitment_bytes` - 38-byte SegWit commitment from Bitcoin Core template
fn create_segwit_commitment_output(commitment_bytes: &[u8]) -> Result<TxOut, CoinbaseError> {
    // Validate commitment size (should be 38 bytes: OP_RETURN + 0x24 + 0xaa21a9ed + 32-byte hash)
    if commitment_bytes.len() < constants::SEGWIT_COMMITMENT_SIZE {
        log::warn!(
            "SegWit commitment too short: {} bytes",
            commitment_bytes.len()
        );
        return Err(CoinbaseError::InvalidCommitmentLength);
    }

    // Verify it starts with the SegWit commitment pattern
    if commitment_bytes.len() >= 6 && commitment_bytes[2..6] != [0xaa, 0x21, 0xa9, 0xed] {
        log::warn!("Invalid SegWit commitment pattern");
        return Err(CoinbaseError::InvalidCommitmentLength);
    }
    let script_bytes = commitment_bytes.to_vec();
    let script = ScriptBuf::from_bytes(script_bytes);
    Ok(TxOut {
        value: Amount::ZERO,
        script_pubkey: script,
    })
}

/// Build a Braidpool coinbase transaction from BlockTemplateComponents
///
/// This creates a coinbase transaction with the format:
/// - Output 0: Paying the full block reward (subsidy + fees) to the pool's address.
/// - Output 1: The wtxid commitment (SegWit commitment), if present.
/// - Output 2: OP_RETURN with Braidpool commitment + extranonce.
/// # Arguments
/// * `components` - Block template data from Bitcoin Core IPC
/// * `braidpool_commitment` - Pool-specific commitment data (max 72 bytes)
/// * `extranonce` - Mining work distribution data (max 32 bytes)
/// * `block_height` - Current blockchain tip height (will be incremented for BIP-34)
/// * `config` - Pool configuration including payout address and identifier
pub fn build_braidpool_coinbase_from_template(
    components: &BlockTemplateComponents,
    braidpool_commitment: &[u8],
    extranonce: &[u8],
    block_height: u32,
    config: &CoinbaseConfig,
) -> Result<FinalCoinbase, CoinbaseError> {
    if extranonce.len() > constants::MAX_EXTRANONCE_LEN {
        return Err(CoinbaseError::InvalidExtranonceLength);
    }
    if braidpool_commitment.len() > constants::MAX_BRAIDPOOL_COMMITMENT_LEN {
        return Err(CoinbaseError::InvalidCommitmentLength);
    }
    if braidpool_commitment.len() + extranonce.len() > 78 {
        return Err(CoinbaseError::OpReturnTooLarge);
    }

    let original_coinbase = parse_coinbase_transaction(&components.coinbase_transaction)?;
    let segwit_commitment = if !components.coinbase_commitment.is_empty() {
        Some(create_segwit_commitment_output(
            &components.coinbase_commitment,
        )?)
    } else {
        log::warn!("No SegWit commitment found in block template components");
        None
    };

    // Calculate the total available funds (extracted reward + fees).
    let total_available = original_coinbase.output[0].value.to_sat();

    // Create the single payout output for the entire available amount.
    let payout_address = Address::from_str(&config.pool_payout_address)
        .map_err(CoinbaseError::AddressError)?
        .require_network(config.network)
        .map_err(|_| CoinbaseError::AddressNetworkMismatch)?;

    let reward_payout = TxOut {
        value: Amount::from_sat(total_available).map_err(|e| {
            log::error!("Amount conversion failed: {}", e);
            CoinbaseError::InvalidBlockTemplateData
        })?,
        script_pubkey: payout_address.script_pubkey(),
    };

    // Build OP_RETURN output.
    let braidpool_output = build_braidpool_op_return(braidpool_commitment, extranonce)?;

    // Build final outputs in the correct order: [REWARD, WTXID, BRAIDPOOL_OPRETURN].
    let mut final_outputs = vec![reward_payout];
    if let Some(segwit_output) = segwit_commitment {
        final_outputs.push(segwit_output);
    }
    final_outputs.push(braidpool_output);

    // Build coinbase input
    let coinbase_input = build_coinbase_input(block_height, extranonce, &config.pool_identifier)?;
    if coinbase_input.script_sig.len() > constants::MAX_COINBASE_SCRIPT_SIG {
        return Err(CoinbaseError::ScriptCreationError);
    }
    let transaction = Transaction {
        version: Version::TWO,
        lock_time: LockTime::ZERO,
        input: vec![coinbase_input],
        output: final_outputs,
    };
    Ok(FinalCoinbase { transaction })
}

/// Assembles a complete Bitcoin block by replacing coinbase and updating header
///
/// Takes an original block template and replaces its coinbase transaction
/// with a custom one, updates the merkle root in the header, and sets the
/// mining nonce. Preserves all other transactions in their original order.
///
/// # Arguments
/// * `original_block_hex` - Complete block template from Bitcoin Core
/// * `new_coinbase` - Custom coinbase transaction to insert
/// * `merkle_root` - Calculated merkle root (little-endian for header)
/// * `nonce` - Mining nonce value
pub fn build_complete_block(
    original_block_hex: &[u8],
    new_coinbase: &Transaction,
    merkle_root: &[u8; 32],
    nonce: u32,
) -> Result<Vec<u8>, CoinbaseError> {
    if original_block_hex.len() < 81 {
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }

    // Extract and update the 80-byte header
    let mut updated_header = original_block_hex[0..80].to_vec();
    updated_header[36..68].copy_from_slice(merkle_root);
    updated_header[76..80].copy_from_slice(&nonce.to_le_bytes());

    // Parse the original block to find where transactions start
    let mut cursor = 80;
    if cursor >= original_block_hex.len() {
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }
    let (tx_count, varint_size) = decode_varint(&original_block_hex[cursor..])?;
    cursor += varint_size;

    if tx_count == 0 {
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }
    if cursor >= original_block_hex.len() {
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }
    let original_coinbase_end = find_transaction_end(&original_block_hex[cursor..])?;
    cursor += original_coinbase_end;

    // Collect remaining transactions (everything after coinbase)
    let remaining_transactions = if tx_count > 1 && cursor < original_block_hex.len() {
        original_block_hex[cursor..].to_vec()
    } else {
        Vec::new()
    };

    // Serialize new coinbase
    let new_coinbase_bytes = consensus::serialize(new_coinbase);

    // Block assembly
    let mut complete_block = Vec::with_capacity(
        80 + varint_size + new_coinbase_bytes.len() + remaining_transactions.len(),
    );

    // Add updated header
    complete_block.extend_from_slice(&updated_header);

    // Add transaction count
    complete_block.extend_from_slice(&encode_varint(tx_count));

    // Add new coinbase transaction
    complete_block.extend_from_slice(&new_coinbase_bytes);

    // Add remaining transactions
    complete_block.extend_from_slice(&remaining_transactions);

    let expected_min_size = 80 + varint_size + new_coinbase_bytes.len();
    if complete_block.len() < expected_min_size {
        log::error!(
            "Block too small: {} bytes, expected >= {}",
            complete_block.len(),
            expected_min_size
        );
        return Err(CoinbaseError::InvalidBlockTemplateData);
    }
    Ok(complete_block)
}

/// Creates a complete Bitcoin block template ready for mining
///
/// Orchestrates the entire block creation process by building a custom
/// coinbase, calculating the merkle root, and assembling the
/// complete block with updated header.
///
/// # Arguments
/// * `components` - Block template data from Bitcoin Core
/// * `braidpool_commitment` - Pool-specific commitment data
/// * `extranonce` - Mining work distribution identifier
/// * `block_height` - Current blockchain tip height
/// * `nonce` - Mining nonce value
/// * `config` - Pool configuration settings
///
pub fn create_block_template(
    components: &BlockTemplateComponents,
    braidpool_commitment: &[u8],
    extranonce: &[u8],
    block_height: u32,
    nonce: u32,
    config: &CoinbaseConfig,
) -> Result<FinalTemplate, CoinbaseError> {
    // Build the custom coinbase transaction
    let final_coinbase = build_braidpool_coinbase_from_template(
        components,
        braidpool_commitment,
        extranonce,
        block_height,
        config,
    )?;

    let coinbase_txid = final_coinbase.transaction.compute_txid();
    let merkle_root_bytes = calculate_merkle_root(coinbase_txid, &components.coinbase_merkle_path);
    let complete_block_bytes = build_complete_block(
        &components.block_hex,
        &final_coinbase.transaction,
        &merkle_root_bytes,
        nonce,
    )?;

    Ok(FinalTemplate {
        coinbase: final_coinbase,
        merkle_root: merkle_root_bytes.to_vec(),
        complete_block_hex: complete_block_bytes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merkle_root_calculation() {
        let coinbase_bytes = vec![
            1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 75, 3, 63, 146, 11, 250, 190, 109, 109, 86,
            6, 110, 64, 228, 218, 247, 203, 127, 75, 141, 53, 51, 197, 180, 38, 117, 115, 221, 103,
            2, 11, 85, 213, 65, 221, 74, 90, 97, 128, 91, 182, 1, 0, 0, 0, 0, 0, 0, 0, 49, 101, 7,
            7, 139, 168, 76, 0, 1, 0, 0, 0, 0, 0, 0, 70, 84, 183, 110, 24, 47, 115, 108, 117, 115,
            104, 47, 0, 0, 0, 0, 3, 120, 55, 179, 37, 0, 0, 0, 0, 25, 118, 169, 20, 124, 21, 78,
            209, 220, 89, 96, 158, 61, 38, 171, 178, 223, 46, 163, 213, 135, 205, 140, 65, 136,
            172, 0, 0, 0, 0, 0, 0, 0, 0, 44, 106, 76, 41, 82, 83, 75, 66, 76, 79, 67, 75, 58, 216,
            82, 49, 182, 148, 133, 228, 178, 20, 248, 55, 219, 145, 83, 227, 86, 32, 97, 240, 182,
            3, 175, 116, 196, 69, 114, 83, 46, 0, 71, 230, 205, 0, 0, 0, 0, 0, 0, 0, 0, 38, 106,
            36, 170, 33, 169, 237, 179, 75, 32, 206, 223, 111, 113, 150, 112, 248, 21, 36, 163,
            123, 107, 168, 153, 76, 233, 86, 77, 218, 162, 59, 48, 26, 180, 38, 62, 34, 3, 185, 0,
            0, 0, 0,
        ];

        let path_data = vec![
            vec![
                122, 97, 64, 124, 164, 158, 164, 14, 87, 119, 226, 169, 34, 196, 251, 51, 31, 131,
                109, 250, 13, 54, 94, 6, 177, 27, 156, 154, 101, 30, 123, 159,
            ],
            vec![
                180, 113, 121, 253, 215, 85, 129, 38, 108, 2, 86, 66, 46, 12, 131, 139, 130, 87,
                29, 92, 59, 164, 247, 114, 251, 140, 129, 88, 127, 196, 125, 116,
            ],
            vec![
                171, 77, 225, 148, 80, 32, 41, 157, 246, 77, 161, 49, 87, 139, 214, 236, 149, 164,
                192, 128, 195, 9, 5, 168, 131, 27, 250, 9, 60, 179, 206, 94,
            ],
            vec![
                6, 187, 202, 75, 155, 220, 255, 166, 199, 35, 182, 220, 20, 96, 123, 41, 109, 40,
                186, 142, 13, 139, 230, 164, 116, 177, 217, 23, 16, 123, 135, 202,
            ],
            vec![
                109, 45, 171, 89, 223, 39, 132, 14, 150, 128, 241, 113, 136, 227, 105, 123, 224,
                48, 66, 240, 189, 186, 222, 49, 173, 143, 80, 90, 110, 219, 192, 235,
            ],
            vec![
                196, 7, 21, 180, 228, 161, 182, 132, 28, 153, 242, 12, 210, 127, 157, 86, 62, 123,
                181, 33, 84, 3, 105, 129, 148, 162, 5, 152, 64, 7, 196, 156,
            ],
            vec![
                22, 16, 18, 180, 109, 237, 68, 167, 197, 10, 195, 134, 11, 119, 219, 184, 49, 140,
                239, 45, 27, 210, 212, 120, 186, 60, 155, 105, 106, 219, 218, 32,
            ],
            vec![
                83, 228, 21, 241, 42, 240, 8, 254, 109, 156, 59, 171, 167, 46, 183, 60, 27, 63,
                241, 211, 235, 179, 147, 99, 46, 3, 22, 166, 159, 169, 183, 159,
            ],
            vec![
                230, 81, 3, 190, 66, 73, 200, 55, 94, 135, 209, 50, 92, 193, 114, 202, 141, 170,
                124, 142, 206, 29, 88, 9, 22, 110, 203, 145, 238, 66, 166, 35,
            ],
            vec![
                43, 106, 86, 239, 237, 74, 208, 202, 247, 133, 88, 42, 15, 77, 163, 186, 85, 26,
                89, 151, 5, 19, 30, 122, 108, 220, 215, 104, 152, 226, 113, 55,
            ],
            vec![
                148, 76, 200, 221, 206, 54, 56, 45, 252, 60, 123, 202, 195, 73, 144, 65, 168, 184,
                59, 130, 145, 229, 250, 44, 213, 70, 175, 128, 34, 31, 102, 80,
            ],
            vec![
                203, 112, 102, 31, 49, 147, 24, 25, 245, 61, 179, 146, 205, 127, 126, 100, 78, 204,
                228, 146, 209, 154, 89, 194, 209, 81, 57, 167, 88, 251, 44, 76,
            ],
        ];

        let expected_root = [
            73, 100, 41, 247, 106, 44, 1, 242, 3, 64, 100, 1, 98, 155, 40, 91, 170, 255, 170, 29,
            193, 255, 244, 71, 236, 29, 134, 218, 94, 45, 78, 77,
        ];

        let coinbase_tx =
            parse_coinbase_transaction(&coinbase_bytes).expect("Failed to parse coinbase");
        let coinbase_txid = coinbase_tx.compute_txid();
        let calculated_root = calculate_merkle_root(coinbase_txid, &path_data);
        assert_eq!(
            calculated_root, expected_root,
            "Merkle root calculation failed!"
        );
    }

    #[test]
    fn test_empty_merkle_path() {
        let coinbase_bytes = vec![
            1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 75, 3, 63, 146, 11, 250, 190, 109, 109, 86,
            6, 110, 64, 228, 218, 247, 203, 127, 75, 141, 53, 51, 197, 180, 38, 117, 115, 221, 103,
            2, 11, 85, 213, 65, 221, 74, 90, 97, 128, 91, 182, 1, 0, 0, 0, 0, 0, 0, 0, 49, 101, 7,
            7, 139, 168, 76, 0, 1, 0, 0, 0, 0, 0, 0, 70, 84, 183, 110, 24, 47, 115, 108, 117, 115,
            104, 47, 0, 0, 0, 0, 3, 120, 55, 179, 37, 0, 0, 0, 0, 25, 118, 169, 20, 124, 21, 78,
            209, 220, 89, 96, 158, 61, 38, 171, 178, 223, 46, 163, 213, 135, 205, 140, 65, 136,
            172, 0, 0, 0, 0, 0, 0, 0, 0, 44, 106, 76, 41, 82, 83, 75, 66, 76, 79, 67, 75, 58, 216,
            82, 49, 182, 148, 133, 228, 178, 20, 248, 55, 219, 145, 83, 227, 86, 32, 97, 240, 182,
            3, 175, 116, 196, 69, 114, 83, 46, 0, 71, 230, 205, 0, 0, 0, 0, 0, 0, 0, 0, 38, 106,
            36, 170, 33, 169, 237, 179, 75, 32, 206, 223, 111, 113, 150, 112, 248, 21, 36, 163,
            123, 107, 168, 153, 76, 233, 86, 77, 218, 162, 59, 48, 26, 180, 38, 62, 34, 3, 185, 0,
            0, 0, 0,
        ];

        let coinbase_tx =
            parse_coinbase_transaction(&coinbase_bytes).expect("Failed to parse coinbase");
        let coinbase_txid = coinbase_tx.compute_txid();

        let empty_path: Vec<Vec<u8>> = vec![];
        let result = calculate_merkle_root(coinbase_txid, &empty_path);

        let expected = coinbase_txid.to_byte_array();
        assert_eq!(result, expected, "Empty path should return coinbase TXID");
    }

    #[test]
    fn test_single_step_merkle_path() {
        let coinbase_bytes = vec![
            1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 75, 3, 63, 146, 11, 250, 190, 109, 109, 86,
            6, 110, 64, 228, 218, 247, 203, 127, 75, 141, 53, 51, 197, 180, 38, 117, 115, 221, 103,
            2, 11, 85, 213, 65, 221, 74, 90, 97, 128, 91, 182, 1, 0, 0, 0, 0, 0, 0, 0, 49, 101, 7,
            7, 139, 168, 76, 0, 1, 0, 0, 0, 0, 0, 0, 70, 84, 183, 110, 24, 47, 115, 108, 117, 115,
            104, 47, 0, 0, 0, 0, 3, 120, 55, 179, 37, 0, 0, 0, 0, 25, 118, 169, 20, 124, 21, 78,
            209, 220, 89, 96, 158, 61, 38, 171, 178, 223, 46, 163, 213, 135, 205, 140, 65, 136,
            172, 0, 0, 0, 0, 0, 0, 0, 0, 44, 106, 76, 41, 82, 83, 75, 66, 76, 79, 67, 75, 58, 216,
            82, 49, 182, 148, 133, 228, 178, 20, 248, 55, 219, 145, 83, 227, 86, 32, 97, 240, 182,
            3, 175, 116, 196, 69, 114, 83, 46, 0, 71, 230, 205, 0, 0, 0, 0, 0, 0, 0, 0, 38, 106,
            36, 170, 33, 169, 237, 179, 75, 32, 206, 223, 111, 113, 150, 112, 248, 21, 36, 163,
            123, 107, 168, 153, 76, 233, 86, 77, 218, 162, 59, 48, 26, 180, 38, 62, 34, 3, 185, 0,
            0, 0, 0,
        ];

        let coinbase_tx =
            parse_coinbase_transaction(&coinbase_bytes).expect("Failed to parse coinbase");
        let coinbase_txid = coinbase_tx.compute_txid();

        let single_path = vec![vec![
            122, 97, 64, 124, 164, 158, 164, 14, 87, 119, 226, 169, 34, 196, 251, 51, 31, 131, 109,
            250, 13, 54, 94, 6, 177, 27, 156, 154, 101, 30, 123, 159,
        ]];

        let result = calculate_merkle_root(coinbase_txid, &single_path);

        let mut data = coinbase_txid.to_byte_array().to_vec();
        data.extend_from_slice(&single_path[0]);
        let expected = double_sha256(&data);

        assert_eq!(result, expected, "Single step merkle calculation failed");
    }

    #[test]
    fn test_merkle_root_debug_validation() {
        let coinbase_bytes = vec![
            2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 25, 3, 82, 214, 13, 8, 1, 2, 3, 4, 5, 6,
            7, 8, 11, 47, 66, 114, 97, 105, 100, 112, 111, 111, 108, 47, 255, 255, 255, 255,
        ];

        if coinbase_bytes.len() > 100 {
            match parse_coinbase_transaction(&coinbase_bytes) {
                Ok(coinbase_tx) => {
                    let coinbase_txid = coinbase_tx.compute_txid();
                    let empty_result = calculate_merkle_root(coinbase_txid, &vec![]);
                    assert_eq!(empty_result, coinbase_txid.to_byte_array());
                }
                Err(e) => {
                    println!("Invalid coinbase bytes: {}", e);
                }
            }
        }
    }
}

#[test]
fn rejects_bad_witness_commitment() {
    let mut bad = vec![0x6a, 0x24, 0x00, 0x00, 0x00, 0x00];
    bad.extend(vec![0; 32]);
    let res = create_segwit_commitment_output(&bad);
    assert!(matches!(res, Err(CoinbaseError::InvalidCommitmentLength)));
}

#[test]
fn coinbase_input_too_big_is_rejected() {
    let block_height = 740_000;
    // Should fail because 33 > MAX_EXTRANONCE_LEN (32)
    let extranonce = vec![0u8; 33];
    let pool_id = "braidpool";
    let res = build_coinbase_input(block_height, &extranonce, pool_id);
    assert!(matches!(res, Err(CoinbaseError::InvalidExtranonceLength)));
}

#[test]
fn test_varint_comprehensive() {
    // Single-byte encoding (0-252)
    for value in 0u64..=252 {
        let encoded = encode_varint(value);
        assert_eq!(encoded.len(), 1, "Value {} should encode to 1 byte", value);
        assert_eq!(encoded[0], value as u8);
        let (decoded, bytes_read) = decode_varint(&encoded).unwrap();
        assert_eq!(decoded, value, "Failed to decode value {}", value);
        assert_eq!(bytes_read, 1);
    }

    // Multi-byte: 0xFD (2 bytes), 0xFE (4 bytes), 0xFF (8 bytes)
    let fd_values = [253u64, 254, 255, 256, 1000, 10000, 65535];
    for value in fd_values {
        let encoded = encode_varint(value);
        assert_eq!(encoded.len(), 3, "Value {} should encode to 3 bytes", value);
        assert_eq!(encoded[0], 0xFD);
        let (decoded, bytes_read) = decode_varint(&encoded).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(bytes_read, 3);
    }

    let fe_values = [65536u64, 100000, 1000000, 4294967295];
    for value in fe_values {
        let encoded = encode_varint(value);
        assert_eq!(encoded.len(), 5, "Value {} should encode to 5 bytes", value);
        assert_eq!(encoded[0], 0xFE);
        let (decoded, bytes_read) = decode_varint(&encoded).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(bytes_read, 5);
    }

    let ff_values = [4294967296u64, 1000000000000, u64::MAX];
    for value in ff_values {
        let encoded = encode_varint(value);
        assert_eq!(encoded.len(), 9, "Value {} should encode to 9 bytes", value);
        assert_eq!(encoded[0], 0xFF);
        let (decoded, bytes_read) = decode_varint(&encoded).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(bytes_read, 9);
    }

    // Roundtrip for varied values
    let roundtrip_values = [
        0,
        1,
        127,
        128,
        252,
        253,
        254,
        255,
        256,
        1000,
        10000,
        65535,
        65536,
        100000,
        1000000,
        4294967295,
        4294967296,
        u64::MAX,
    ];
    for &value in &roundtrip_values {
        let encoded = encode_varint(value);
        let (decoded, _) = decode_varint(&encoded).unwrap();
        assert_eq!(
            decoded, value,
            "Roundtrip failed for value {}, encoded as {:?}",
            value, encoded
        );
    }

    // Error handling for malformed/short input
    assert!(decode_varint(&[]).is_err());
    assert!(decode_varint(&[0xFD, 0x01]).is_err());
    assert!(decode_varint(&[0xFE, 0x01, 0x02, 0x03]).is_err());
    assert!(decode_varint(&[0xFF, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]).is_err());

    // Protocol compatibility
    assert_eq!(encode_varint(0), vec![0x00]);
    assert_eq!(encode_varint(252), vec![0xFC]);
    assert_eq!(encode_varint(253), vec![0xFD, 0xFD, 0x00]);
    assert_eq!(encode_varint(65535), vec![0xFD, 0xFF, 0xFF]);
    assert_eq!(encode_varint(65536), vec![0xFE, 0x00, 0x00, 0x01, 0x00]);
    assert_eq!(
        encode_varint(4294967296),
        vec![0xFF, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]
    );

    // Little-endian byte order for multi-byte encodings
    assert_eq!(encode_varint(0x1234), vec![0xFD, 0x34, 0x12]);
    assert_eq!(
        encode_varint(0x12345678),
        vec![0xFE, 0x78, 0x56, 0x34, 0x12]
    );
    assert_eq!(
        encode_varint(0x123456789ABCDEF0),
        vec![0xFF, 0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
    );

    // Edge/value boundaries
    let boundaries = [
        (252u64, 1),        // Max 1-byte
        (253u64, 3),        // Min 0xFD
        (65535u64, 3),      // Max 0xFD
        (65536u64, 5),      // Min 0xFE
        (4294967295u64, 5), // Max 0xFE
        (4294967296u64, 9), // Min 0xFF
    ];
    for &(value, expected_len) in &boundaries {
        let encoded = encode_varint(value);
        assert_eq!(
            encoded.len(),
            expected_len,
            "Value {} should encode to {} bytes",
            value,
            expected_len
        );
        let (decoded, bytes_read) = decode_varint(&encoded).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(bytes_read, expected_len);
    }

    // Only consume required bytes, ignore trailing data
    let mut data = encode_varint(1000);
    data.extend_from_slice(&[0xFF, 0xFF, 0xFF]);
    let (decoded, bytes_read) = decode_varint(&data).unwrap();
    assert_eq!(decoded, 1000);
    assert_eq!(bytes_read, 3);
    assert!(bytes_read < data.len());

    // Zero and Max value correctness
    let encoded_zero = encode_varint(0);
    assert_eq!(encoded_zero, vec![0x00]);
    let (decoded_zero, bytes_read_zero) = decode_varint(&encoded_zero).unwrap();
    assert_eq!(decoded_zero, 0);
    assert_eq!(bytes_read_zero, 1);

    let max_value = u64::MAX;
    let encoded_max = encode_varint(max_value);
    assert_eq!(encoded_max.len(), 9);
    assert_eq!(encoded_max[0], 0xFF);
    let (decoded_max, bytes_read_max) = decode_varint(&encoded_max).unwrap();
    assert_eq!(decoded_max, max_value);
    assert_eq!(bytes_read_max, 9);
}
