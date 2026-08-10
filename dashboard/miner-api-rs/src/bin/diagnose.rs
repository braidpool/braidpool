use miner_api_rs::scanner;
use std::{net::IpAddr, str::FromStr};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let arg = std::env::args().nth(1);
    match arg.as_deref() {
        None => {
            let miners = scanner::scan_lan().await;
            print_miners(&miners);
        }
        Some(target) if target.contains('/') => {
            let miners = scanner::scan_subnet(target).await?;
            print_miners(&miners);
        }
        Some(target) => {
            let ip =
                IpAddr::from_str(target).map_err(|_| anyhow::anyhow!("invalid IP: {target}"))?;
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

fn print_miners(miners: &[Box<dyn miner_api_rs::asic_rs::core::traits::miner::Miner>]) {
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
