//! Cpunet implementation
//Referenced - https://github.com/braidpool/rust-bitcoin/tree/cpunet
use bitcoin::{
    bech32,
    block::Header,
    hashes::{sha256d, Hash, HashEngine},
    BlockHash, ScriptBuf, WitnessProgram,
};
use core::fmt;
use std::str::FromStr;

use crate::error::{CpunetAddressError, ParseCpunetError};

/// Human-readable part for cpunet bech32 addresses: "tc"
pub const CPUNET_HRP: &str = "tc";

/// The core-arg name along with that the actual network name as string-slice
pub const CPUNET_NAME: &str = "cpunet";

/// Implementation of Cpunet specific `Network` and `Address` decoding/encoding functionality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Cpunet;

impl Cpunet {
    #[inline]
    fn is_cpunet_name(name: &str) -> bool {
        name.eq_ignore_ascii_case(CPUNET_NAME)
    }

    #[inline]
    pub fn is_cpunet_hrp(hrp: &str) -> bool {
        hrp.eq_ignore_ascii_case(CPUNET_HRP)
    }

    /// Encodes a witness program as a cpunet bech32m or bech32 address depending upon `WitnessVersion` for non-taproot and taproot specific addresses.
    pub fn encode_bech32_address(program: &WitnessProgram) -> String {
        let hrp = bech32::Hrp::parse_unchecked(CPUNET_HRP);
        let version = bech32::Fe32::try_from(program.version().to_num())
            .expect("witness version is valid fe32");
        bech32::segwit::encode(hrp, version, program.program().as_bytes())
            .expect("valid witness program encodes successfully")
    }

    /// Decodes a cpunet bech32 address string.
    ///
    /// The script pubkey (ScriptBuf) for the decoded address
    pub fn decode_bech32_address(address: &str) -> Result<ScriptBuf, CpunetAddressError> {
        let (hrp, version, data) =
            bech32::segwit::decode(address).map_err(CpunetAddressError::Bech32)?;

        // Verify HRP is cpunet
        if !hrp.as_str().eq_ignore_ascii_case(CPUNET_HRP) {
            return Err(CpunetAddressError::WrongNetwork {
                expected: CPUNET_HRP.to_string(),
                found: hrp.to_string(),
            });
        }

        let witness_version = bitcoin::WitnessVersion::try_from(version.to_u8())
            .map_err(|_| CpunetAddressError::InvalidWitnessVersion(version.to_u8()))?;
        let witness_program = WitnessProgram::new(witness_version, &data)
            .map_err(CpunetAddressError::InvalidProgram)?;

        Ok(ScriptBuf::new_witness_program(&witness_program))
    }
    /// Returns the block hash.
    pub fn block_hash(header: &Header) -> BlockHash {
        let mut engine = sha256d::Hash::engine();
        engine.input(&header.version.to_consensus().to_le_bytes());
        engine.input(header.prev_blockhash.as_byte_array());
        engine.input(header.merkle_root.as_byte_array());
        engine.input(&header.time.to_le_bytes());
        engine.input(&header.bits.to_consensus().to_le_bytes());
        engine.input(&header.nonce.to_le_bytes());
        engine.input("cpunet\0".as_bytes());

        BlockHash::from_byte_array(sha256d::Hash::from_engine(engine).to_byte_array())
    }
}

impl fmt::Display for Cpunet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CPUNET_NAME)
    }
}

impl FromStr for Cpunet {
    type Err = ParseCpunetError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if Cpunet::is_cpunet_name(s) {
            Ok(Cpunet)
        } else {
            Err(ParseCpunetError(s.to_owned()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::{absolute::Time, constants::genesis_block, params::Params, WitnessVersion};

    #[test]
    fn cpunet_hrp_check() {
        assert!(Cpunet::is_cpunet_hrp("tc"));
        assert!(Cpunet::is_cpunet_hrp("TC"));
        assert!(!Cpunet::is_cpunet_hrp("bc"));
        assert!(!Cpunet::is_cpunet_hrp("tb"));
    }

    #[test]
    fn cpunet_from_str() {
        assert!(Cpunet::from_str("cpunet").is_ok());
        assert!(Cpunet::from_str("mainnet").is_err());
    }

    #[test]
    fn cpunet_address_roundtrip() {
        let program_bytes = [0u8; 20];
        let program =
            WitnessProgram::new(WitnessVersion::V0, &program_bytes).expect("valid witness program");

        let address = Cpunet::encode_bech32_address(&program);
        assert!(address.starts_with("tc1"));

        let decoded_script = Cpunet::decode_bech32_address(&address).expect("should decode");
        assert!(decoded_script.is_witness_program());
        let expected_script = bitcoin::ScriptBuf::new_witness_program(&program);
        assert_eq!(decoded_script, expected_script);
    }

    #[test]
    fn cpunet_wrong_network_address() {
        let mainnet_addr = "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4";
        let result = Cpunet::decode_bech32_address(mainnet_addr);
        assert!(matches!(
            result,
            Err(CpunetAddressError::WrongNetwork { .. })
        ));
    }
    #[test]
    fn compute_genesis_hash_cpunet() {
        let mut cpunet_genesis_block = genesis_block(Params::TESTNET4);
        cpunet_genesis_block.header.time =
            Time::from_consensus(1723652721).unwrap().to_consensus_u32();
        cpunet_genesis_block.header.nonce = 961348305;
        let header_hash_bytes: &[u8; 32] = &[
            155, 244, 9, 169, 207, 188, 132, 171, 5, 153, 89, 228, 109, 99, 3, 243, 57, 98, 248, 5,
            188, 141, 147, 51, 119, 165, 255, 187, 0, 0, 0, 0,
        ];
        assert_eq!(
            Cpunet::block_hash(&cpunet_genesis_block.header).as_byte_array(),
            header_hash_bytes
        );
    }
}
