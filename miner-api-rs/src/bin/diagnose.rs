use miner_asicrs::scanner;
use std::{net::IpAddr, str::FromStr};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let arg = std::env::args().nth(1);
    match arg.as_deref() {
        None => {
            match scanner::scan_lan().await {
                Ok(miners) => print_miners(&miners),
                Err(e) => println!("Error: {e}"),
            }
        }
        Some(target) if target.contains('/') => {
            match scanner::scan_subnet(target).await {
                Ok(miners) => print_miners(&miners),
                Err(e) => println!("Error: {e}"),
            }
        }
        Some(target) => {
            let ip = IpAddr::from_str(target)
                .map_err(|_| anyhow::anyhow!("invalid IP: {target}"))?;
            match scanner::scan_ip(ip).await? {
                Some(m) => {
                    let info = m.get_device_info();
                    println!("{} {} at {}", info.make, info.model, m.get_ip());
                }
                None => println!("no miner at {ip}"),
            }
        }
    }

    Ok(())
}

fn print_miners(miners: &[Box<dyn miner_asicrs::asic_rs::core::traits::miner::Miner>]) {
    if miners.is_empty() {
        println!("  no miners found");
    } else {
        println!("  {} miner(s):", miners.len());
        for m in miners {
            let info = m.get_device_info();
            println!("    {} {} at {}", info.make, info.model, m.get_ip());
        }
    }
}
