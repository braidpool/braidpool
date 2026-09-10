"""Configuration for one Braidpool functional test script."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(slots=True)
class NetworkConfig:
    """Tunable parameters for a functional test network."""

    #Node number config
    num_braidpool_nodes: int = 1
    num_cpu_miners: int = 0

    #Chain config
    network: str = "regtest"
    initial_blocks: int = 101


    bitcoin_rpc_port: int | None = None
    bitcoin_p2p_port: int | None = None
    bitcoin_ipc_socket: Path | None = None
    
    #Binary paths
    bitcoin_bin_path: Path | None = None
    braidpool_bin_path: Path | None = None
    minerd_bin_path: Path | None = None

    # Timeouts 
    startup_timeout_braidpool: float = 30.0
    startup_timeout_btc: float = 90.0
    startup_timeout_minerd: float = 60.0

    rpc_timeout: float = 10.0
    peer_connection_timeout: float = 15.0
    bead_propagation_timeout: float = 60.0

    #Logging config
    log_level: str = "INFO"
    random_seed: int = 42
