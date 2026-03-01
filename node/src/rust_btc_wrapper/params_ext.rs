//! Referenced from https://github.com/rust-bitcoin/rust-bitcoin

use bitcoin::{network::Network, BlockHeight, BlockHeightInterval, Target, TestnetVersion};

use crate::rust_btc_wrapper::network_ext::NetworkExtension;

#[derive(Debug, Clone)]
pub struct Params {
    pub network: NetworkExtension,
    pub bip16_time: u32,
    pub bip34_height: BlockHeight,
    pub bip65_height: BlockHeight,
    pub bip66_height: BlockHeight,
    pub enforce_bip94: bool,
    pub rule_change_activation_threshold: BlockHeightInterval,
    pub miner_confirmation_window: BlockHeightInterval,
    pub pow_limit: Target,
    pub max_attainable_target: Target,
    pub pow_target_spacing: u32,
    pub pow_target_timespan: u32,
    pub allow_min_difficulty_blocks: bool,
    pub no_pow_retargeting: bool,
}

pub static MAINNET: Params = Params::MAINNET;
#[deprecated(since = "TBD", note = "use `TESTNET3` instead")]
pub static TESTNET: Params = Params::TESTNET3;
pub static TESTNET3: Params = Params::TESTNET3;
pub static TESTNET4: Params = Params::TESTNET4;
pub static SIGNET: Params = Params::SIGNET;
pub static REGTEST: Params = Params::REGTEST;
pub static CPUNET: Params = Params::CPUNET;

#[allow(deprecated)]
impl Params {
    /// The mainnet parameters (alias for `Params::MAINNET`).
    pub const BITCOIN: Self = Self::MAINNET;

    /// The mainnet parameters.
    pub const MAINNET: Self = Self {
        network: NetworkExtension::Standard(bitcoin::Network::Bitcoin),
        bip16_time: 1333238400,                      // Apr 1 2012
        bip34_height: BlockHeight::from_u32(227931), // 000000000000024b89b42a942fe0d9fea3bb44ab7bd1b19115dd6a759c0808b8
        bip65_height: BlockHeight::from_u32(388381), // 000000000000000004c2b624ed5d7756c508d90fd0da2c7c679febfa6c4735f0
        bip66_height: BlockHeight::from_u32(363725), // 00000000000000000379eaa19dce8c9b722d46ae6a57c2f1a988119488b50931
        enforce_bip94: false,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(1916), // 95%
        miner_confirmation_window: BlockHeightInterval::from_u32(2016),
        pow_limit: Target::MAX_ATTAINABLE_MAINNET,
        max_attainable_target: Target::MAX_ATTAINABLE_MAINNET,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: false,
        no_pow_retargeting: false,
    };

    /// The testnet3 parameters.
    #[deprecated(since = "TBD", note = "use `TESTNET3` instead")]
    pub const TESTNET: Self = Self {
        network: NetworkExtension::Standard(Network::Testnet(TestnetVersion::V3)),
        bip16_time: 1333238400,                      // Apr 1 2012
        bip34_height: BlockHeight::from_u32(21111), // 0000000023b3a96d3484e5abb3755c413e7d41500f8e2a5c3f0dd01299cd8ef8
        bip65_height: BlockHeight::from_u32(581885), // 00000000007f6655f22f98e72ed80d8b06dc761d5da09df0fa1dc4be4f861eb6
        bip66_height: BlockHeight::from_u32(330776), // 000000002104c8c45e99a8853285a3b592602a3ccde2b832481da85e9e4ba182
        enforce_bip94: false,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(1512), // 75%
        miner_confirmation_window: BlockHeightInterval::from_u32(2016),
        pow_limit: Target::MAX_ATTAINABLE_TESTNET,
        max_attainable_target: Target::MAX_ATTAINABLE_TESTNET,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: true,
        no_pow_retargeting: false,
    };

    /// The testnet3 parameters.
    pub const TESTNET3: Self = Self {
        network: NetworkExtension::Standard(Network::Testnet(TestnetVersion::V3)),
        bip16_time: 1333238400,                      // Apr 1 2012
        bip34_height: BlockHeight::from_u32(21111), // 0000000023b3a96d3484e5abb3755c413e7d41500f8e2a5c3f0dd01299cd8ef8
        bip65_height: BlockHeight::from_u32(581885), // 00000000007f6655f22f98e72ed80d8b06dc761d5da09df0fa1dc4be4f861eb6
        bip66_height: BlockHeight::from_u32(330776), // 000000002104c8c45e99a8853285a3b592602a3ccde2b832481da85e9e4ba182
        enforce_bip94: false,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(1512), // 75%
        miner_confirmation_window: BlockHeightInterval::from_u32(2016),
        pow_limit: Target::MAX_ATTAINABLE_TESTNET,
        max_attainable_target: Target::MAX_ATTAINABLE_TESTNET,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: true,
        no_pow_retargeting: false,
    };

    /// The testnet4 parameters.
    pub const TESTNET4: Self = Self {
        network: NetworkExtension::Standard(Network::Testnet(TestnetVersion::V4)),
        bip16_time: 1333238400, // Apr 1 2012
        bip34_height: BlockHeight::from_u32(1),
        bip65_height: BlockHeight::from_u32(1),
        bip66_height: BlockHeight::from_u32(1),
        enforce_bip94: true,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(1512), // 75%
        miner_confirmation_window: BlockHeightInterval::from_u32(2016),
        pow_limit: Target::MAX_ATTAINABLE_TESTNET,
        max_attainable_target: Target::MAX_ATTAINABLE_TESTNET,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: true,
        no_pow_retargeting: false,
    };

    /// The signet parameters.
    pub const SIGNET: Self = Self {
        network: NetworkExtension::Standard(Network::Signet),
        bip16_time: 1333238400, // Apr 1 2012
        bip34_height: BlockHeight::from_u32(1),
        bip65_height: BlockHeight::from_u32(1),
        bip66_height: BlockHeight::from_u32(1),
        enforce_bip94: false,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(1916), // 95%
        miner_confirmation_window: BlockHeightInterval::from_u32(2016),
        pow_limit: Target::MAX_ATTAINABLE_SIGNET,
        max_attainable_target: Target::MAX_ATTAINABLE_SIGNET,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: false,
        no_pow_retargeting: false,
    };

    /// The regtest parameters.
    pub const REGTEST: Self = Self {
        network: NetworkExtension::Standard(Network::Regtest),
        bip16_time: 1333238400,                         // Apr 1 2012
        bip34_height: BlockHeight::from_u32(100000000), // not activated on regtest
        bip65_height: BlockHeight::from_u32(1351),
        bip66_height: BlockHeight::from_u32(1251), // used only in rpc tests
        enforce_bip94: false,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(108), // 75%
        miner_confirmation_window: BlockHeightInterval::from_u32(144),
        pow_limit: Target::MAX_ATTAINABLE_REGTEST,
        max_attainable_target: Target::MAX_ATTAINABLE_REGTEST,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: true,
        no_pow_retargeting: true,
    };

    /// The cpunet parameters.
    pub const CPUNET: Params = Self {
        network: NetworkExtension::Cpunet,
        bip16_time: 1333238400, // Apr 1 2012
        bip34_height: BlockHeight::from_u32(1),
        bip65_height: BlockHeight::from_u32(1),
        bip66_height: BlockHeight::from_u32(1),
        enforce_bip94: false,
        rule_change_activation_threshold: BlockHeightInterval::from_u32(1512), // 75%
        miner_confirmation_window: BlockHeightInterval::from_u32(2016),
        pow_limit: Target::MAX_ATTAINABLE_MAINNET,
        max_attainable_target: Target::MAX_ATTAINABLE_MAINNET,
        pow_target_spacing: 10 * 60,            // 10 minutes.
        pow_target_timespan: 14 * 24 * 60 * 60, // 2 weeks.
        allow_min_difficulty_blocks: false,
        no_pow_retargeting: false,
    };

    /// Constructs parameters set for the given network.
    pub const fn new(network: NetworkExtension) -> Self {
        match network {
            NetworkExtension::Standard(Network::Bitcoin) => Self::MAINNET,
            NetworkExtension::Standard(Network::Testnet(TestnetVersion::V3)) => Self::TESTNET3,
            NetworkExtension::Standard(Network::Testnet(TestnetVersion::V4)) => Self::TESTNET4,
            NetworkExtension::Standard(Network::Testnet(_)) => Self::TESTNET3,
            NetworkExtension::Standard(Network::Signet) => Self::SIGNET,
            NetworkExtension::Standard(Network::Regtest) => Self::REGTEST,
            NetworkExtension::Standard(_) => Self::MAINNET, // Default for unknown standard networks
            NetworkExtension::Cpunet => Params::CPUNET,
        }
    }

    /// Calculates the number of blocks between difficulty adjustments.
    pub fn difficulty_adjustment_interval(&self) -> u32 {
        self.pow_target_timespan / self.pow_target_spacing
    }
}

impl From<NetworkExtension> for Params {
    fn from(value: NetworkExtension) -> Self {
        Self::new(value)
    }
}

impl From<&NetworkExtension> for Params {
    fn from(value: &NetworkExtension) -> Self {
        Self::new(*value)
    }
}

impl From<NetworkExtension> for &'static Params {
    fn from(value: NetworkExtension) -> Self {
        value.params()
    }
}

impl From<&NetworkExtension> for &'static Params {
    fn from(value: &NetworkExtension) -> Self {
        value.params()
    }
}

impl AsRef<Self> for Params {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl AsRef<Params> for NetworkExtension {
    fn as_ref(&self) -> &Params {
        Self::params(*self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_network_extension_to_params() {
        let tests = vec![
            (NetworkExtension::Standard(Network::Bitcoin), &MAINNET),
            (
                NetworkExtension::Standard(Network::Testnet(TestnetVersion::V3)),
                &TESTNET3,
            ),
            (
                NetworkExtension::Standard(Network::Testnet(TestnetVersion::V4)),
                &TESTNET4,
            ),
            (NetworkExtension::Standard(Network::Signet), &SIGNET),
            (NetworkExtension::Standard(Network::Regtest), &REGTEST),
            (NetworkExtension::Cpunet, &CPUNET),
        ];

        for (network_ext, expected) in tests {
            let params: Params = Params::from(network_ext);
            assert_eq!(params.network, expected.network);
            assert_eq!(params.pow_target_spacing, expected.pow_target_spacing);
            assert_eq!(
                params.allow_min_difficulty_blocks,
                expected.allow_min_difficulty_blocks
            );
        }
    }

    #[test]
    fn from_network_extension_ref_to_params() {
        let tests = vec![
            (NetworkExtension::Standard(Network::Bitcoin), &MAINNET),
            (
                NetworkExtension::Standard(Network::Testnet(TestnetVersion::V3)),
                &TESTNET3,
            ),
            (NetworkExtension::Cpunet, &CPUNET),
        ];

        for (network_ext, expected) in tests {
            let params: Params = Params::from(&network_ext);
            assert_eq!(params.network, expected.network);
        }
    }

    #[test]
    fn from_network_extension_to_static_params() {
        let tests = vec![
            (NetworkExtension::Standard(Network::Bitcoin), &MAINNET),
            (
                NetworkExtension::Standard(Network::Testnet(TestnetVersion::V4)),
                &TESTNET4,
            ),
            (NetworkExtension::Standard(Network::Regtest), &REGTEST),
            (NetworkExtension::Cpunet, &CPUNET),
        ];

        for (network_ext, expected) in tests {
            let params: &'static Params = network_ext.into();
            assert!(std::ptr::eq(params, expected));
        }
    }

    #[test]
    fn from_network_extension_ref_to_static_params() {
        let network_ext = NetworkExtension::Standard(Network::Signet);
        let params: &'static Params = (&network_ext).into();
        assert!(std::ptr::eq(params, &SIGNET));

        let cpunet = NetworkExtension::Cpunet;
        let params: &'static Params = (&cpunet).into();
        assert!(std::ptr::eq(params, &CPUNET));
    }

    #[test]
    fn as_ref_returns_correct_params() {
        let tests = vec![
            (NetworkExtension::Standard(Network::Bitcoin), &MAINNET),
            (NetworkExtension::Standard(Network::Signet), &SIGNET),
            (NetworkExtension::Cpunet, &CPUNET),
        ];

        for (network_ext, expected) in tests {
            let params: &Params = network_ext.as_ref();
            assert!(std::ptr::eq(params, expected));
        }
    }
}
