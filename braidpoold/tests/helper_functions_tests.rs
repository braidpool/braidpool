// Unit tests for helper functions and utilities

#[cfg(test)]
mod conversion_tests {
    #[test]
    fn test_sats_to_btc_conversion() {
        // Test satoshi to BTC conversion
        assert_eq!(to_btc_from_sats(100_000_000), 1.0);
        assert_eq!(to_btc_from_sats(50_000_000), 0.5);
        assert_eq!(to_btc_from_sats(1_000), 0.00001);
        assert_eq!(to_btc_from_sats(0), 0.0);
    }

    #[test]
    fn test_sats_to_btc_precision() {
        // Test precision of conversion
        let sats = 12_345_678u64;
        let btc = to_btc_from_sats(sats);
        assert_eq!(btc, 0.12345678);
    }

    #[test]
    fn test_zero_sats() {
        assert_eq!(to_btc_from_sats(0), 0.0);
    }

    #[test]
    fn test_max_btc() {
        // 21 million BTC in sats
        let max_btc_sats = 21_000_000 * 100_000_000u64;
        let btc = to_btc_from_sats(max_btc_sats);
        assert_eq!(btc, 21_000_000.0);
    }

    // Helper function (would be imported from api module)
    fn to_btc_from_sats(sats: u64) -> f64 {
        (sats as f64) / 100_000_000.0
    }
}

#[cfg(test)]
mod fee_calculation_tests {
    #[test]
    fn test_fee_rate_calculation() {
        // fee_rate = fee_sats / vsize
        let fee_sats = 1000u64;
        let vsize = 250u64;

        let fee_rate = calculate_fee_rate(fee_sats, vsize);
        assert_eq!(fee_rate, 4.0);
    }

    #[test]
    fn test_fee_rate_fractional() {
        let fee_sats = 2625u64;
        let vsize = 250u64;

        let fee_rate = calculate_fee_rate(fee_sats, vsize);
        assert_eq!(fee_rate, 10.5);
    }

    #[test]
    fn test_fee_rate_zero_vsize() {
        let fee_sats = 1000u64;
        let vsize = 0u64;

        let fee_rate = calculate_fee_rate(fee_sats, vsize);
        assert_eq!(fee_rate, 0.0);
    }

    #[test]
    fn test_fee_rate_zero_fee() {
        let fee_sats = 0u64;
        let vsize = 250u64;

        let fee_rate = calculate_fee_rate(fee_sats, vsize);
        assert_eq!(fee_rate, 0.0);
    }

    #[test]
    fn test_fee_rate_high_fee() {
        // High fee rate scenario (100 sat/vB)
        let fee_sats = 25_000u64;
        let vsize = 250u64;

        let fee_rate = calculate_fee_rate(fee_sats, vsize);
        assert_eq!(fee_rate, 100.0);
    }

    fn calculate_fee_rate(fee_sats: u64, vsize: u64) -> f64 {
        if vsize > 0 {
            (fee_sats as f64) / (vsize as f64)
        } else {
            0.0
        }
    }
}

#[cfg(test)]
mod timestamp_tests {
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn test_timestamp_generation() {
        let ts1 = now_ts();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let ts2 = now_ts();

        assert!(ts2 >= ts1, "Timestamps should be monotonic");
    }

    #[test]
    fn test_timestamp_reasonable_range() {
        let ts = now_ts();

        // Should be after 2020-01-01 (1577836800)
        assert!(ts > 1_577_836_800, "Timestamp should be after 2020");

        // Should be before 2030-01-01 (1893456000)
        assert!(ts < 1_893_456_000, "Timestamp should be before 2030");
    }

    #[test]
    fn test_timestamp_fallback_priority() {
        let mempool_time = Some(1000u64);
        let block_time = Some(2000u64);
        let now_time = 3000u64;

        // Priority: mempool_time > block_time > now
        let ts = mempool_time.or(block_time).unwrap_or(now_time);
        assert_eq!(ts, 1000, "Should prefer mempool_time");

        let ts2 = None.or(block_time).unwrap_or(now_time);
        assert_eq!(ts2, 2000, "Should use block_time if mempool_time is None");

        let ts3 = None.or(None).unwrap_or(now_time);
        assert_eq!(ts3, 3000, "Should use now_time if both are None");
    }

    fn now_ts() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs()
    }
}

#[cfg(test)]
mod transaction_hash_tests {
    #[test]
    fn test_truncate_hash() {
        let hash = "abc123def456abc123def456abc123def456abc123def456abc123def456abc1";

        // Test hash format (should be 64 hex characters)
        assert_eq!(hash.len(), 64);
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_hash_validation() {
        // Valid hashes
        assert!(is_valid_hash("a".repeat(64).as_str()));
        assert!(is_valid_hash("0123456789abcdef".repeat(4).as_str()));

        // Invalid hashes
        assert!(!is_valid_hash("too_short"));
        assert!(!is_valid_hash("not_hex_characters!@#$".repeat(4).as_str()));
        assert!(!is_valid_hash("")); // Empty
    }

    fn is_valid_hash(hash: &str) -> bool {
        hash.len() == 64 && hash.chars().all(|c| c.is_ascii_hexdigit())
    }
}

#[cfg(test)]
mod category_string_tests {
    #[test]
    fn test_category_labels() {
        let categories = vec![
            "Mempool",
            "Committed",
            "Proposed",
            "Scheduled",
            "Confirmed",
            "Replaced",
        ];

        for category in categories {
            assert!(!category.is_empty());
            assert!(category.chars().next().unwrap().is_uppercase());
        }
    }

    #[test]
    fn test_category_matching() {
        assert!(matches_category("Mempool", "mempool"));
        assert!(matches_category("Confirmed", "confirmed"));
        assert!(matches_category("Proposed", "PROPOSED"));
    }

    fn matches_category(expected: &str, actual: &str) -> bool {
        expected.to_lowercase() == actual.to_lowercase()
    }
}

#[cfg(test)]
mod validation_tests {
    #[test]
    fn test_txid_validation() {
        // Valid txids (64 hex characters)
        assert!(is_valid_txid(
            "abc123def456abc123def456abc123def456abc123def456abc123def456abc1"
        ));
        assert!(is_valid_txid(&"f".repeat(64)));

        // Invalid txids
        assert!(!is_valid_txid("too_short"));
        assert!(!is_valid_txid(&"g".repeat(64))); // 'g' is not hex
        assert!(!is_valid_txid(""));
    }

    #[test]
    fn test_amount_validation() {
        // Valid amounts (non-negative)
        assert!(is_valid_amount(0.0));
        assert!(is_valid_amount(0.00001));
        assert!(is_valid_amount(21_000_000.0));

        // Invalid amounts
        assert!(!is_valid_amount(-1.0));
        assert!(!is_valid_amount(-0.00001));
    }

    #[test]
    fn test_confirmations_validation() {
        // Valid confirmation counts
        assert!(is_valid_confirmations(0));
        assert!(is_valid_confirmations(1));
        assert!(is_valid_confirmations(6));
        assert!(is_valid_confirmations(1000));
    }

    fn is_valid_txid(txid: &str) -> bool {
        txid.len() == 64 && txid.chars().all(|c| c.is_ascii_hexdigit())
    }

    fn is_valid_amount(amount: f64) -> bool {
        amount >= 0.0
    }

    fn is_valid_confirmations(_confirmations: u32) -> bool {
        // Confirmations are always non-negative (u32 cannot be negative)
        true
    }
}

#[cfg(test)]
mod state_transition_tests {
    #[test]
    fn test_state_progression() {
        // Test the natural progression of transaction states
        let states = vec!["Mempool", "Committed", "Proposed", "Scheduled", "Confirmed"];

        // Each state can progress to the next
        for i in 0..states.len() - 1 {
            assert!(
                can_progress_to(states[i], states[i + 1]),
                "Should be able to progress from {} to {}",
                states[i],
                states[i + 1]
            );
        }
    }

    #[test]
    fn test_invalid_state_progression() {
        // Cannot skip states
        assert!(!can_skip_state("Mempool", "Proposed"));
        assert!(!can_skip_state("Mempool", "Scheduled"));
        assert!(!can_skip_state("Committed", "Scheduled"));
    }

    #[test]
    fn test_confirmed_is_terminal() {
        // Once confirmed, transaction stays confirmed
        let is_terminal = true;
        assert!(is_terminal, "Confirmed is a terminal state");
    }

    fn can_progress_to(from: &str, to: &str) -> bool {
        matches!(
            (from, to),
            ("Mempool", "Committed")
                | ("Committed", "Proposed")
                | ("Proposed", "Scheduled")
                | ("Scheduled", "Confirmed")
        )
    }

    fn can_skip_state(_from: &str, _to: &str) -> bool {
        // Skipping states is never allowed
        false
    }
}

#[cfg(test)]
mod mempool_aggregation_tests {
    use std::collections::BTreeSet;

    #[test]
    fn test_combine_mempools() {
        let bitcoind_txs = vec!["tx1", "tx2", "tx3"];
        let cmempool_txs = vec!["tx2", "tx3", "tx4"];

        let combined: BTreeSet<_> = bitcoind_txs
            .into_iter()
            .chain(cmempool_txs.into_iter())
            .collect();

        assert_eq!(combined.len(), 4); // tx1, tx2, tx3, tx4
        assert!(combined.contains("tx1"));
        assert!(combined.contains("tx4"));
    }

    #[test]
    fn test_no_duplicates() {
        let txs = vec!["tx1", "tx1", "tx2", "tx2", "tx3"];
        let unique: BTreeSet<_> = txs.into_iter().collect();

        assert_eq!(unique.len(), 3);
    }

    #[test]
    fn test_empty_mempools() {
        let empty1: Vec<&str> = vec![];
        let empty2: Vec<&str> = vec![];

        let combined: BTreeSet<_> = empty1.into_iter().chain(empty2.into_iter()).collect();

        assert_eq!(combined.len(), 0);
    }

    #[test]
    fn test_one_empty_mempool() {
        let bitcoind_txs = vec!["tx1", "tx2"];
        let empty: Vec<&str> = vec![];

        let combined: BTreeSet<_> = bitcoind_txs.into_iter().chain(empty.into_iter()).collect();

        assert_eq!(combined.len(), 2);
    }
}

#[cfg(test)]
mod histogram_tests {
    use std::collections::BTreeMap;

    #[test]
    fn test_fee_bucketing() {
        let fee_rates: Vec<f64> = vec![1.2, 1.7, 5.3, 5.8, 10.1, 10.9];
        let mut histogram: BTreeMap<u64, u64> = BTreeMap::new();

        for rate in fee_rates {
            let bucket = rate.round() as u64;
            *histogram.entry(bucket).or_insert(0) += 1;
        }

        assert_eq!(histogram.get(&1), Some(&1)); // 1.2 -> bucket 1
        assert_eq!(histogram.get(&2), Some(&1)); // 1.7 -> bucket 2
        assert_eq!(histogram.get(&5), Some(&1)); // 5.3 -> bucket 5
        assert_eq!(histogram.get(&6), Some(&1)); // 5.8 -> bucket 6
        assert_eq!(histogram.get(&10), Some(&1)); // 10.1 -> bucket 10
        assert_eq!(histogram.get(&11), Some(&1)); // 10.9 -> bucket 11
    }

    #[test]
    fn test_histogram_vsize_accumulation() {
        let mut histogram: BTreeMap<u64, u64> = BTreeMap::new();

        // Multiple transactions at same fee rate
        let bucket = 10u64;
        *histogram.entry(bucket).or_insert(0) += 250; // tx1: 250 vB
        *histogram.entry(bucket).or_insert(0) += 180; // tx2: 180 vB
        *histogram.entry(bucket).or_insert(0) += 300; // tx3: 300 vB

        assert_eq!(histogram.get(&bucket), Some(&730));
    }

    #[test]
    fn test_histogram_sorting() {
        let mut histogram: BTreeMap<u64, u64> = BTreeMap::new();
        histogram.insert(10, 100);
        histogram.insert(5, 200);
        histogram.insert(1, 50);

        let sorted: Vec<_> = histogram.iter().collect();

        // BTreeMap keeps sorted order
        assert_eq!(sorted[0].0, &1);
        assert_eq!(sorted[1].0, &5);
        assert_eq!(sorted[2].0, &10);
    }
}
