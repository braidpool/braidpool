use bitcoin::absolute::MedianTimePast;
use bitcoin::{Amount, CompactTarget, Network, Params, Target, Work};
use core::ops::Add;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::error::Error;
//Containing functionality related to difficulty adjustment for braidpool currently static
//TODO: currently it will only be placeholder for modifying min_target accordingly for weaker_difficulty

pub struct DifficultyAdjuster {
    /// Current client difficulty setting
    pub current_difficulty: Target,
    /// Previous difficulty before a change
    pub old_difficulty: Target,
}
pub trait DifficultyAdjustmentTrait {
    fn get_current_difficulty(&self) -> Target;
    fn get_new_difficulty(&mut self, initial_target: Option<CompactTarget>) -> Target;
    fn new() -> Self;
}
impl DifficultyAdjustmentTrait for DifficultyAdjuster {
    fn new() -> Self {
        let zero_work = Target::ZERO;
        Self {
            current_difficulty: zero_work,
            //At initialization this shall be work computed according to `start_target` but for time being it is taken as Work(0)
            old_difficulty: zero_work,
        }
    }
    fn get_current_difficulty(&self) -> Target {
        self.current_difficulty
    }
    fn get_new_difficulty(&mut self, initial_target: Option<CompactTarget>) -> Target {
        if let Some(start_target) = initial_target {
            self.current_difficulty = Target::from_compact(start_target);
            self.old_difficulty = Target::from_compact(start_target);
        };
        self.current_difficulty
    }
}
impl DifficultyAdjuster {
    pub fn new() -> Self {
        let zero_work = Target::ZERO;
        Self {
            current_difficulty: zero_work,
            old_difficulty: zero_work,
        }
    }
}
#[derive(Debug)]
pub enum PayoutCommands {
    UpdatePayoutHeap {
        bead_timestamp: MedianTimePast,
        payout_address: String,
        work: Work,
    },
    GeneratePayout {
        payout_sender: std::sync::mpsc::Sender<Vec<OutputPair>>,
        total_difficulty: f64,
        total_amount: Amount,
    },
}
#[derive(Debug)]
pub struct Payout {
    //Intializing mapping heap that will listen for new beads and update accordingly
    //Sorted mapping of only required information instead of complete `Bead` which will be updated on the arrival of beads
    payout_heap: BinaryHeap<(MedianTimePast, (Work, String))>,
    //Payout command receiver
    payout_cmd_receiver: std::sync::mpsc::Receiver<PayoutCommands>,
    //Configured network wrt which payout is being generated
    configured_network: Network,
}
#[derive(Debug, Clone)]
pub struct OutputPair {
    pub address: bitcoin::Address,
    pub amount: bitcoin::Amount,
}

impl Payout {
    pub fn new(configured_network: Network) -> (Self, std::sync::mpsc::Sender<PayoutCommands>) {
        let (payout_cmd_tx, payout_cmd_rx) = std::sync::mpsc::channel::<PayoutCommands>();
        (
            Payout {
                payout_heap: BinaryHeap::new(),
                payout_cmd_receiver: payout_cmd_rx,
                configured_network,
            },
            payout_cmd_tx,
        )
    }
    //Address::Work for beads belonging to same address
    fn _compute_work_mapping(&self) -> Result<HashMap<String, Work>, Box<dyn Error + Send + Sync>> {
        let mut work_mapping: HashMap<String, Work> = HashMap::new();
        for (_bead_timestamp, (bead_work, miner_payout_address)) in self.payout_heap.iter() {
            if work_mapping.contains_key(miner_payout_address) {
                if let Some(existing_work) = work_mapping.get_mut(miner_payout_address) {
                    *existing_work = Add::add(*existing_work, *bead_work);
                }
            } else {
                work_mapping.insert(miner_payout_address.clone(), *bead_work);
            }
        }
        Ok(work_mapping)
    }
    fn get_difficulty_window_shares(
        &self,
        total_difficulty: f64,
    ) -> Result<Vec<(String, f64)>, Box<dyn Error + Send + Sync>> {
        let mut result_values: Vec<(String, f64)> = Vec::new();
        let mut running_difficulty: f64 = 0.0;
        let network_params = match self.configured_network {
            Network::Bitcoin => Params::BITCOIN,
            Network::CPUNet => Params::CPUNET,
            Network::Regtest => Params::REGTEST,
            Network::Signet => Params::SIGNET,
            Network::Testnet(bitcoin::TestnetVersion::V4) => Params::TESTNET4,
            Network::Testnet(bitcoin::TestnetVersion::V3) => Params::TESTNET3,
            _ => Params::MAINNET,
        };
        // Query shares in batches going back in time
        for (_bead_timestamp, (bead_work, miner_payout_address)) in self.payout_heap.iter() {
            let curr_bead_difficulty = bead_work
                .to_target()
                .difficulty_float(network_params.clone());
            if running_difficulty < total_difficulty {
                running_difficulty += curr_bead_difficulty;
                result_values.push((miner_payout_address.clone(), curr_bead_difficulty));
            } else {
                break;
            }
        }
        Ok(result_values)
    }
    pub fn payout_runner(&mut self) {
        while let Ok(payout_cmd) = self.payout_cmd_receiver.recv() {
            tracing::info!("Payout runner initialize and received command succesfully");
            match payout_cmd {
                PayoutCommands::GeneratePayout {
                    payout_sender,
                    total_difficulty,
                    total_amount,
                } => {
                    let payout_distribution = match self
                        .get_output_distribuition(total_difficulty, total_amount)
                    {
                        Ok(reward_distribution) => reward_distribution,
                        Err(error) => {
                            tracing::error!(
                                    "An error occurred while generating payout distribution - {}, skipping generation.",
                                    error
                                );
                            continue;
                        }
                    };
                    match payout_sender.send(payout_distribution) {
                        Ok(_) => {
                            tracing::info!(
                                "Payout distribution sent to template_creator successfully !"
                            );
                        }
                        Err(_) => {
                            tracing::error!(
                                "An error occurred while sending payout distrubtion to downstream"
                            );
                        }
                    }
                }
                PayoutCommands::UpdatePayoutHeap {
                    bead_timestamp,
                    payout_address,
                    work,
                } => {
                    self.payout_heap
                        .push((bead_timestamp, (work, payout_address)));
                }
            }
        }
    }
    fn group_shares_by_address(address_work_pairs: &[(String, f64)]) -> HashMap<String, f64> {
        let mut address_difficulty_map = HashMap::new();
        for (address, bead_work) in address_work_pairs {
            *address_difficulty_map.entry(address.clone()).or_insert(0.0) += bead_work;
        }
        address_difficulty_map
    }
    fn append_proportional_distribution(
        address_difficulty_map: HashMap<String, f64>,
        total_amount: bitcoin::Amount,
        distribution: &mut Vec<OutputPair>,
    ) -> Result<(), Box<dyn Error + Send + Sync>> {
        let total_difficulty: f64 = address_difficulty_map.values().sum();
        let mut distributed_amount = bitcoin::Amount::ZERO;

        for (i, (address_str, difficulty)) in address_difficulty_map.iter().enumerate() {
            let address = address_str
                .parse::<bitcoin::Address<_>>()
                .map_err(|e| format!("Invalid bitcoin address '{address_str}': {e}"))?
                .assume_checked();

            let amount: Amount = if i == address_difficulty_map.len() - 1 {
                // Last address gets remainder to handle rounding
                let left_amount = core::ops::Sub::sub(total_amount, distributed_amount).unwrap();
                left_amount
            } else {
                let proportion = *difficulty / total_difficulty;
                let amount_sats = (total_amount.to_sat() as f64 * proportion).round() as u64;
                bitcoin::Amount::from_sat(amount_sats).unwrap()
            };

            distributed_amount = core::ops::Add::add(distributed_amount, amount).unwrap();
            distribution.push(OutputPair { address, amount });
        }
        Ok(())
    }
    fn get_output_distribuition(
        &self,
        total_difficulty: f64,
        total_amount: bitcoin::Amount,
    ) -> Result<Vec<OutputPair>, Box<dyn Error + Send + Sync>> {
        let beads = self.get_difficulty_window_shares(total_difficulty)?;
        if beads.is_empty() {
            return Ok(vec![]);
        }
        let mut distribution = Vec::<OutputPair>::with_capacity(beads.len());

        let address_difficulty_map = Self::group_shares_by_address(&beads);
        Self::append_proportional_distribution(
            address_difficulty_map,
            total_amount,
            &mut distribution,
        )?;
        Ok(distribution)
    }
}

#[cfg(test)]
mod tests {
    use std::time::UNIX_EPOCH;

    use super::*;
    use bitcoin::absolute::MedianTimePast;
    use bitcoin::pow::CompactTargetExt;
    use bitcoin::{Amount, Network, Target, Work};

    fn work_from_compact(compact: bitcoin::CompactTarget) -> Work {
        let target = Target::from_compact(compact);
        target.to_work()
    }

    #[test]
    fn test_group_shares_by_address_single_address() {
        let pairs = vec![
            (
                "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
                1.0,
            ),
            (
                "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
                2.0,
            ),
            (
                "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
                3.0,
            ),
        ];
        let map = Payout::group_shares_by_address(&pairs);
        assert_eq!(map.len(), 1);
        assert_eq!(
            map.get("tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z")
                .copied()
                .unwrap_or(0.0),
            6.0
        );
    }

    #[test]
    fn test_group_shares_by_address_multiple_addresses() {
        let pairs = vec![
            (
                "tc1q7trhdr48sjm2p3lpcjvyqv49gu3yztuff0pqg9".to_string(),
                1.0,
            ),
            (
                "tc1qe4f5g0d4cmh97ypn2zdzcd8kp5a57ak0xp4v37".to_string(),
                2.0,
            ),
            (
                "tc1q7trhdr48sjm2p3lpcjvyqv49gu3yztuff0pqg9".to_string(),
                3.5,
            ),
            (
                "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
                1.5,
            ),
        ];
        let map = Payout::group_shares_by_address(&pairs);
        assert_eq!(map.len(), 3);
        assert_eq!(
            map.get("tc1q7trhdr48sjm2p3lpcjvyqv49gu3yztuff0pqg9")
                .copied()
                .unwrap_or(0.0),
            4.5
        );
        assert_eq!(
            map.get("tc1qe4f5g0d4cmh97ypn2zdzcd8kp5a57ak0xp4v37")
                .copied()
                .unwrap_or(0.0),
            2.0
        );
        assert_eq!(
            map.get("tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z")
                .copied()
                .unwrap_or(0.0),
            1.5
        );
    }

    #[test]
    fn test_group_shares_by_address_empty() {
        let pairs: Vec<(String, f64)> = vec![];
        let map = Payout::group_shares_by_address(&pairs);
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_append_proportional_distribution_equal_difficulty() {
        let mut distribution = Vec::new();
        let mut map = std::collections::HashMap::new();
        map.insert(
            "tc1qe4f5g0d4cmh97ypn2zdzcd8kp5a57ak0xp4v37".to_string(),
            1.0,
        );
        map.insert(
            "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
            1.0,
        );
        let total_amount = Amount::from_sat(100).unwrap();

        Payout::append_proportional_distribution(map, total_amount, &mut distribution)
            .expect("append should succeed");

        assert_eq!(distribution.len(), 2);
        let sum: u64 = distribution.iter().map(|o| o.amount.to_sat()).sum();
        assert_eq!(sum, 100);
    }
    #[test]
    fn test_payout_command_update_heap() {
        let (mut payout, tx) = Payout::new(Network::CPUNet);

        let handle = std::thread::spawn(move || {
            payout.payout_runner();
            payout
        });

        let compact = bitcoin::CompactTarget::from_hex("0x1d00ffff").unwrap();
        let w = work_from_compact(compact);
        let now = MedianTimePast::from_u32(
            std::time::SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs() as u32,
        )
        .unwrap();

        tx.send(PayoutCommands::UpdatePayoutHeap {
            bead_timestamp: now,
            payout_address: "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
            work: w,
        })
        .unwrap();
        //Dropping the channel sender to break infinite loop of runner after updating command is processed forceably
        drop(tx);
        let payout = handle.join().unwrap();
        assert!(!payout.payout_heap.is_empty());
        let heap_top = &payout.payout_heap.peek().unwrap().1;
        assert_eq!(
            heap_top.1,
            "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string()
        );
        println!(
            "Work - {}",
            heap_top.0.to_target().difficulty(Params::CPUNET)
        );
    }

    #[test]
    fn test_append_proportional_distribution_different_difficulty() {
        let mut distribution = Vec::new();
        let mut map = std::collections::HashMap::new();
        map.insert(
            "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
            1.0,
        );
        map.insert(
            "tc1qe4f5g0d4cmh97ypn2zdzcd8kp5a57ak0xp4v37".to_string(),
            3.0,
        );
        let total_amount = Amount::from_sat(100).unwrap();

        Payout::append_proportional_distribution(map, total_amount, &mut distribution)
            .expect("append should succeed");

        // 1:3 ratio means 25% and 75%
        assert_eq!(distribution.len(), 2);
        let sum: u64 = distribution.iter().map(|o| o.amount.to_sat()).sum();
        assert_eq!(sum, 100);
    }

    #[test]
    fn test_append_proportional_distribution_rounding_with_remainder() {
        let mut distribution = Vec::new();
        let mut map = std::collections::HashMap::new();
        map.insert(
            "tc1qkuw7jx4f5m9vd7kdm4cfz0vgdxsrg6vr0xd25z".to_string(),
            1.0,
        );
        map.insert(
            "tc1q7trhdr48sjm2p3lpcjvyqv49gu3yztuff0pqg9".to_string(),
            1.0,
        );
        let total_amount = Amount::from_sat(101).unwrap(); // odd satoshi to test remainder

        Payout::append_proportional_distribution(map, total_amount, &mut distribution)
            .expect("append should succeed");

        assert_eq!(distribution.len(), 2);
        let sum: u64 = distribution.iter().map(|o| o.amount.to_sat()).sum();
        assert_eq!(sum, 101); // All sats must be distributed
    }

    #[test]
    fn test_append_proportional_distribution_invalid_address() {
        let mut distribution = Vec::new();
        let mut map = std::collections::HashMap::new();
        map.insert("invalid_addr".to_string(), 1.0);
        let total_amount = Amount::from_sat(100).unwrap();

        let result = Payout::append_proportional_distribution(map, total_amount, &mut distribution);
        assert!(result.is_err());
    }

    #[test]
    fn test_get_output_distribution_empty_heap() {
        let (payout, _tx) = Payout::new(Network::CPUNet);
        let out = payout
            .get_output_distribuition(1000.0, Amount::from_sat(100).unwrap())
            .unwrap();
        assert!(out.is_empty());
    }

    #[test]
    fn test_get_output_distribution_zero_total_difficulty() {
        let (payout, _tx) = Payout::new(Network::CPUNet);
        let out = payout
            .get_output_distribuition(0.0, Amount::from_sat(100).unwrap())
            .unwrap();
        assert!(out.is_empty());
    }

    #[test]
    fn test_get_difficulty_window_shares_empty_heap() {
        let (payout, _tx) = Payout::new(Network::CPUNet);
        let shares = payout.get_difficulty_window_shares(1.0).unwrap();
        assert!(shares.is_empty());
    }

    #[test]
    fn test_get_difficulty_window_shares_single_bead() {
        let (mut payout, _tx) = Payout::new(Network::CPUNet);

        let compact = bitcoin::CompactTarget::from_hex("0x1d00ffff").unwrap();
        let w = work_from_compact(compact);
        let current_system_time = std::time::SystemTime::now();
        let duration_since_epoch = match current_system_time.duration_since(UNIX_EPOCH) {
            Ok(duration) => duration,
            Err(error) => {
                panic!("{}", error);
            }
        };
        let now = MedianTimePast::from_u32(duration_since_epoch.as_secs() as u32).unwrap();
        payout.payout_heap.push((
            now,
            (w, "tc1q7trhdr48sjm2p3lpcjvyqv49gu3yztuff0pqg9".to_string()),
        ));

        let shares = payout.get_difficulty_window_shares(0.0000001).unwrap();
        assert!(!shares.is_empty());
        assert_eq!(shares.len(), 1);
        assert_eq!(shares[0].0, "tc1q7trhdr48sjm2p3lpcjvyqv49gu3yztuff0pqg9");
    }

    #[test]
    fn test_get_difficulty_window_shares_respects_limit() {
        let (mut payout, _tx) = Payout::new(Network::CPUNet);

        let compact = bitcoin::CompactTarget::from_hex("0x1d00ffff").unwrap();
        let w = work_from_compact(compact);
        //Current UNIX timestamp during broadcast of bead
        let current_system_time = std::time::SystemTime::now();
        let duration_since_epoch = match current_system_time.duration_since(UNIX_EPOCH) {
            Ok(duration) => duration,
            Err(error) => {
                panic!("{}", error);
            }
        };
        let now = MedianTimePast::from_u32(duration_since_epoch.as_secs() as u32).unwrap();

        for i in 0..5 {
            payout.payout_heap.push((now, (w, format!("addr{}", i))));
        }

        let shares = payout.get_difficulty_window_shares(0.00000001).unwrap();
        assert!(!shares.is_empty());
        assert!(shares.len() <= 5);
    }

    #[test]
    fn test_difficulty_adjuster_creation() {
        let adjuster = DifficultyAdjuster::new();
        assert_eq!(adjuster.current_difficulty, Target::ZERO);
        assert_eq!(adjuster.old_difficulty, Target::ZERO);
    }

    #[test]
    fn test_difficulty_adjuster_trait_get_current() {
        let adjuster = DifficultyAdjuster::new();
        assert_eq!(adjuster.get_current_difficulty(), Target::ZERO);
    }

    #[test]
    fn test_difficulty_adjuster_trait_get_new_difficulty_with_target() {
        let mut adjuster = DifficultyAdjuster::new();
        let compact = bitcoin::CompactTarget::from_hex("0x1d00ffff").unwrap();
        let new_diff = adjuster.get_new_difficulty(Some(compact));
        assert_eq!(new_diff, Target::from_compact(compact));
        assert_eq!(adjuster.current_difficulty, Target::from_compact(compact));
        assert_eq!(adjuster.old_difficulty, Target::from_compact(compact));
    }

    #[test]
    fn test_difficulty_adjuster_trait_get_new_difficulty_none() {
        let mut adjuster = DifficultyAdjuster::new();
        let new_diff = adjuster.get_new_difficulty(None);
        assert_eq!(new_diff, Target::ZERO);
    }

    #[test]
    fn test_payout_creation() {
        let (payout, _tx) = Payout::new(Network::Bitcoin);
        assert_eq!(payout.configured_network, Network::Bitcoin);
    }

    #[test]
    fn test_output_pair_creation() {
        let addr_str = "tc1qtrru7yc0gx48vusca35jyvzh0xvgle8c0m8fy6";
        let addr = addr_str
            .parse::<bitcoin::Address<_>>()
            .unwrap()
            .assume_checked();
        let amount = Amount::from_sat(1000).unwrap();

        let pair = OutputPair {
            address: addr,
            amount,
        };
        assert_eq!(pair.amount.to_sat(), 1000);
    }
}
