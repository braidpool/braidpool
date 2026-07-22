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
            warn!("arp -a failed: {e}");
            return Vec::new();
        }
    };
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
                if !ip.is_broadcast() && !ip.is_multicast() && !ip.is_loopback() {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_windows_arp() {
        let input = "\
Interface: 192.168.1.5 --- 0x11
  Internet Address      Physical Address      Type
  192.168.1.1           00-50-56-e0-27-c3     dynamic
  192.168.1.10          00-50-56-ee-fd-46     dynamic
  192.168.1.255         ff-ff-ff-ff-ff-ff     static
  224.0.0.22            01-00-5e-00-00-16     static
";
        let hosts = parse_arp_output(input);
        assert_eq!(
            hosts,
            vec![
                "192.168.1.1".parse::<Ipv4Addr>().unwrap(),
                "192.168.1.10".parse::<Ipv4Addr>().unwrap(),
            ]
        );
    }

    #[test]
    fn parse_linux_arp() {
        let input = "\
Address         HWtype  HWaddress           Flags Mask     Iface
192.168.1.1     ether   00:50:56:e0:27:c3   C              eth0
192.168.1.50    ether   00:50:56:ee:fd:46   C              eth0
";
        let hosts = parse_arp_output(input);
        assert_eq!(
            hosts,
            vec![
                "192.168.1.1".parse::<Ipv4Addr>().unwrap(),
                "192.168.1.50".parse::<Ipv4Addr>().unwrap(),
            ]
        );
    }

    #[test]
    fn parse_linux_arp_paren_format() {
        let input = "\
? (192.168.1.1) at 00:50:56:e0:27:c3 [ether] on eth0
? (192.168.1.50) at 00:50:56:ee:fd:46 [ether] on eth0
";
        let hosts = parse_arp_output(input);
        assert_eq!(
            hosts,
            vec![
                "192.168.1.1".parse::<Ipv4Addr>().unwrap(),
                "192.168.1.50".parse::<Ipv4Addr>().unwrap(),
            ]
        );
    }
}
