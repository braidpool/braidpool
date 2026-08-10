use std::net::Ipv4Addr;
use std::process::Command;
use std::str::FromStr;
use tracing::{debug, warn};

pub fn is_wsl() -> bool {
    if std::env::var("WSL_DISTRO_NAME").is_ok() || std::env::var("WSLENV").is_ok() {
        return true;
    }
    std::fs::read_to_string("/proc/version")
        .map(|v| v.to_lowercase().contains("microsoft"))
        .unwrap_or(false)
}

pub fn arp_hosts() -> Vec<Ipv4Addr> {
    let cmd = if is_wsl() { "arp.exe" } else { "arp" };
    let output = match Command::new(cmd).arg("-a").output() {
        Ok(o) => o,
        Err(e) => {
            warn!(cmd = %cmd, error = %e, "failed to run arp -a");
            return Vec::new();
        }
    };
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        warn!(
            "{cmd} -a exited with {status}; stderr: {stderr}",
            status = output.status,
        );
    }
    parse_arp_output(&String::from_utf8_lossy(&output.stdout))
}

fn parse_arp_output(text: &str) -> Vec<Ipv4Addr> {
    let mut addrs = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty()
            || trimmed.starts_with("Interface:")
            || trimmed.starts_with("Internet")
            || trimmed.starts_with("Address")
        {
            continue;
        }
        for token in trimmed.split_whitespace() {
            let candidate = token.trim_matches(|c| c == '(' || c == ')');
            if let Ok(ip) = Ipv4Addr::from_str(candidate) {
                if !ip.is_broadcast()
                    && !ip.is_multicast() // 224.0.0.0/4
                    && !ip.is_loopback() // 127.x.x.x
                    && !ip.is_unspecified()
                // 0.0.0.0
                {
                    debug!(ip = %ip, "ARP host");
                    addrs.push(ip);
                }
                break;
            }
        }
    }
    addrs.sort();
    addrs.dedup();
    addrs
}
