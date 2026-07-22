use miner_asicrs::scanner;

#[tokio::test]
async fn test_lan_scan() {
    match scanner::scan_lan().await {
        Ok(miners) => {
            println!("Found {} miners", miners.len());
            for miner in &miners {
                let info = miner.get_device_info();
                println!("  {} {} at {}", info.make, info.model, miner.get_ip());
            }
        }
        Err(e) => println!("Scan failed: {}", e),
    }
}
