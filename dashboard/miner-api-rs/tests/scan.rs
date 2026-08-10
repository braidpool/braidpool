use miner_api_rs::scanner;

#[tokio::test]
#[ignore = "requires LAN access and real miner hardware"]
async fn test_lan_scan() {
    let miners = scanner::scan_lan().await;
    println!("Found {} miners", miners.len());
    for miner in &miners {
        let info = miner.get_device_info();
        println!("  {} {} at {}", info.make, info.model, miner.get_ip());
    }
}
