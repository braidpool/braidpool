use crate::arp_hosts;
use asic_rs::MinerFactory;
use futures::StreamExt;
use std::net::IpAddr;
use tracing::{debug, info, warn};

pub async fn scan_lan() -> Vec<Box<dyn asic_rs::core::traits::miner::Miner>> {
    let hosts = match tokio::task::spawn_blocking(arp_hosts).await {
        Ok(hosts) => hosts,
        Err(e) => {
            warn!(error = %e, "failed to read ARP table");
            return Vec::new();
        }
    };
    if hosts.is_empty() {
        warn!("ARP table is empty");
        return Vec::new();
    }
    info!("{} ARP host(s) — probing", hosts.len());
    scan_ips(hosts.into_iter().map(IpAddr::V4)).await
}

pub async fn scan_ips(
    ips: impl IntoIterator<Item = IpAddr>,
) -> Vec<Box<dyn asic_rs::core::traits::miner::Miner>> {
    let factory = MinerFactory::new();
    futures::stream::iter(ips)
        .map(|ip| {
            let f = &factory;
            async move {
                debug!(ip = %ip, "probing");
                (ip, f.get_miner(ip).await)
            }
        })
        .buffer_unordered(256)
        .filter_map(|(ip, r)| async move {
            match r {
                Ok(Some(m)) => Some(m),
                Ok(None) => None,
                Err(e) => {
                    warn!(ip = %ip, error = %e, "probe failed");
                    None
                }
            }
        })
        .collect::<Vec<_>>()
        .await
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
