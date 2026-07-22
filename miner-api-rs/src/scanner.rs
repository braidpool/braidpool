use crate::arp_hosts;
use asic_rs::MinerFactory;
use futures::StreamExt;
use std::net::IpAddr;
use thiserror::Error;
use tracing::{debug, info, warn};

#[derive(Debug, Error)]
pub enum ScanError {
    #[error("scan failed: {0}")]
    Scan(#[from] anyhow::Error),
}

pub async fn scan_lan() -> Result<Vec<Box<dyn asic_rs::core::traits::miner::Miner>>, ScanError> {
    let hosts = arp_hosts();
    if hosts.is_empty() {
        warn!("ARP table is empty — try scan_subnet(\"192.168.x.x/24\") instead.");
        return Ok(Vec::new());
    }
    info!("{} ARP host(s) — probing", hosts.len());
    Ok(scan_ips(hosts.into_iter().map(IpAddr::V4)).await?)
}

pub async fn scan_ips(
    ips: impl IntoIterator<Item = IpAddr>,
) -> Result<Vec<Box<dyn asic_rs::core::traits::miner::Miner>>, anyhow::Error> {
    let factory = MinerFactory::new();
    let results = futures::stream::iter(ips)
        .map(|ip| {
            let f = &factory;
            async move {
                debug!(ip = %ip, "probing");
                f.get_miner(ip).await
            }
        })
        .buffer_unordered(64)
        .filter_map(|r| async move { r.ok().flatten() })
        .collect::<Vec<_>>()
        .await;
    Ok(results)
}

pub async fn scan_ip(
    ip: IpAddr,
) -> Result<Option<Box<dyn asic_rs::core::traits::miner::Miner>>, anyhow::Error> {
    MinerFactory::new().get_miner(ip).await
}

pub async fn scan_subnet(
    cidr: &str,
) -> Result<Vec<Box<dyn asic_rs::core::traits::miner::Miner>>, anyhow::Error> {
    MinerFactory::from_subnet(cidr)?
        .with_concurrent_limit(256)
        .scan()
        .await
}
