"""Deterministic port allocation for functional test scripts."""

from __future__ import annotations

import logging
import socket
import threading
from dataclasses import dataclass

from test_framework.logging_utils import log_event, log_exception


logger = logging.getLogger(__name__)

class PortAllocationError(RuntimeError):
    """Raised when a deterministic test port cannot be allocated."""


class PortSeed:
    """Global port seed set by the functional test runner."""

    n: int = 0


@dataclass(frozen=True, slots=True)
class PortAllocation:
    component: str
    offset: int
    port: int


class PortPool:
    """Allocate ports from a deterministic per-test range.

    Ports are chosen as:

        BASE_PORT + (portseed * PORTS_PER_TEST) + offset

    The bind probe is a sanity check only. It does not determine uniqueness.
    """

    
    BASE_PORT = 16000
    PORTS_PER_TEST = 100

    _COMPONENT_RANGES = {
        "bitcoin_rpc": range(0, 5),
        "bitcoin_p2p": range(5, 10),
        "braidpool_p2p": range(10, 40),
        "braidpool_rpc": range(40, 70),
        "braidpool_stratum": range(70, 90),
        "helper": range(90, 100),
    }

    def __init__(
        self,
        port_seed: int | None = None,
        *,
        base_port: int = BASE_PORT,
        ports_per_test: int = PORTS_PER_TEST,
        validate_ports: bool = True,
    ) -> None:
        if port_seed is None:
            port_seed = PortSeed.n
        if port_seed < 0:
            raise ValueError(f"port_seed must be >= 0, got {port_seed}")
        if ports_per_test < self.PORTS_PER_TEST:
            raise ValueError(
                f"ports_per_test must be at least {self.PORTS_PER_TEST}, got {ports_per_test}"
            )

        self.port_seed = port_seed
        self.base_port = base_port
        self.ports_per_test = ports_per_test
        self.validate_ports = validate_ports
        self.test_range_start = base_port + (port_seed * ports_per_test)
        self.test_range_end = self.test_range_start + ports_per_test - 1
        self._next_by_component = {
            component: offsets.start for component, offsets in self._COMPONENT_RANGES.items()
        }
        self._allocated: dict[int, PortAllocation] = {}
        self._manual: dict[int, str] = {}
        self._lock = threading.Lock()
        if self.validate_ports:
            self._check_ephemeral_overlap()
        log_event(
            logger,
            "port_pool_initialized",
            level=logging.DEBUG,
            port_seed=self.port_seed,
            range_start=self.test_range_start,
            range_end=self.test_range_end,
            validate_ports=self.validate_ports,
        )

    def allocate(self, component: str = "helper", node_id: int | None = None) -> int:
        """Allocate one deterministic port for *component*."""
        with self._lock:
            offsets = self._component_offsets(component)
            offset = self._next_by_component[component]
            if node_id is not None:
                offset = offsets.start + node_id
            if offset not in offsets:
                raise PortAllocationError(
                    f"No port offsets left for component={component!r}; "
                    f"portseed={self.port_seed}, range={self.test_range_start}-{self.test_range_end}"
                )

            port = self._port_for_offset(offset)
            self._validate_available(port, component, offset)
            self._allocated[port] = PortAllocation(component, offset, port)
            self._next_by_component[component] = max(self._next_by_component[component], offset + 1)
            log_event(
                logger,
                "port_allocated",
                level=logging.DEBUG,
                component=component,
                node_id=node_id,
                offset=offset,
                port=port,
                port_seed=self.port_seed,
            )
            return port

    def allocate_many(self, component: str, count: int) -> list[int]:
        """Allocate *count* ports for *component*."""
        if count < 1:
            raise ValueError(f"count must be >= 1, got {count}")
        return [self.allocate(component) for _ in range(count)]

    # Manual reservation is supported for cases where the test needs to specify exact ports, such as when configuring Bitcoin Core RPC or P2P ports.
    def reserve_manual(self, component: str, ports: list[int]) -> None:
        """Reserve user-supplied ports and detect local collisions."""
        with self._lock:
            for port in ports:
                if port in self._allocated:
                    allocation = self._allocated[port]
                    raise PortAllocationError(
                        f"Manual port {port} for {component!r} collides with "
                        f"auto port for {allocation.component!r} at offset {allocation.offset}"
                    )
                if port in self._manual:
                    raise PortAllocationError(
                        f"Manual port {port} for {component!r} already reserved by "
                        f"{self._manual[port]!r}"
                    )
                self._validate_bindable(port, component, "manual")
                self._manual[port] = component
                log_event(logger, "manual_port_reserved", level=logging.DEBUG, component=component, port=port)

    @property
    def band(self) -> tuple[int, int]:
        """Return the deterministic port range for this test script."""
        return self.test_range_start, self.test_range_end

    @property
    def allocated_ports(self) -> list[int]:
        """Return auto-allocated ports in allocation order."""
        return list(self._allocated)

    def _component_offsets(self, component: str) -> range:
        try:
            return self._COMPONENT_RANGES[component]
        except KeyError as exc:
            valid = ", ".join(sorted(self._COMPONENT_RANGES))
            raise ValueError(f"Unknown port component {component!r}; valid: {valid}") from exc

    def _port_for_offset(self, offset: int) -> int:
        return self.test_range_start + offset

    # The following methods perform sanity checks to validate that allocated or manually reserved ports are not in use by other processes for early detection. 
    def _validate_available(self, port: int, component: str, offset: int) -> None:
        if port in self._allocated:
            allocation = self._allocated[port]
            raise PortAllocationError(
                f"Port {port} already allocated to {allocation.component!r}; "
                f"requested component={component!r}, offset={offset}"
            )
        if port in self._manual:
            raise PortAllocationError(
                f"Port {port} for component={component!r}, offset={offset} collides "
                f"with manual port for {self._manual[port]!r}"
            )
        self._validate_bindable(port, component, offset)

    @staticmethod
    def _bind_probe(port: int) -> None:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.bind(("127.0.0.1", port))

    def _validate_bindable(self, port: int, component: str, offset: int | str) -> None:
        if not self.validate_ports:
            return
        try:
            self._bind_probe(port)
        except OSError as exc:
            log_exception(logger, "port_bind_probe_failed", exc, port=port, component=component, offset=offset)
            raise PortAllocationError(
                f"Port {port} is not bindable for component={component!r}, "
                f"offset={offset!r}: {exc}"
            ) from exc

    # Sanity check to detect misconfiguration that would cause test ports to overlap with the kernel ephemeral range.
    def _check_ephemeral_overlap(self) -> None:
        ephemeral = self._linux_ephemeral_range()
        if ephemeral is None:
            return
        start, end = ephemeral
        if self.test_range_start <= end and self.test_range_end >= start:
            log_event(
                logger,
                "ephemeral_port_range_overlap",
                level=logging.ERROR,
                range_start=self.test_range_start,
                range_end=self.test_range_end,
                ephemeral_start=start,
                ephemeral_end=end,
            )
            raise PortAllocationError(
                f"Configured test port range {self.test_range_start}-{self.test_range_end} "
                f"overlaps kernel ephemeral range {start}-{end}. Choose a different base port."
            )

    @staticmethod
    def _linux_ephemeral_range() -> tuple[int, int] | None:
        try:
            with open("/proc/sys/net/ipv4/ip_local_port_range", encoding="utf8") as f:
                raw = f.read()
        except OSError:
            return None
        parts = raw.split()
        if len(parts) != 2:
            return None
        try:
            return int(parts[0]), int(parts[1])
        except ValueError:
            return None
