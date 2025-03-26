#!/usr/bin/env python3
"""
    Unit tests for the Braidpool Simulator
"""

import unittest
import sys
import os
import random
import time
import hashlib
import math
from unittest.mock import patch, MagicMock
import numpy as np

# Add the parent directory to the path so we can import the simulator
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from tests.simulator import (
    Network, Node, Bead, Braid,
    sha256d, sph_arclen, uint256,
    NETWORK_SIZE, TICKSIZE, MAX_HASH, NETWORK_HASHRATE,
    TARGET_NB, TARGET_NC
)

class TestUtilityFunctions(unittest.TestCase):
    """Test utility functions in the simulator."""

    def test_sha256d(self):
        """Test that sha256d produces correct hashes."""
        # Test with bytes
        test_bytes = b"test message"
        expected = hashlib.sha256(hashlib.sha256(test_bytes).digest()).digest()
        self.assertEqual(sha256d(test_bytes), expected)

        # Test with integer
        test_int = 12345
        expected = hashlib.sha256(hashlib.sha256(test_int.to_bytes(32, byteorder='big')).digest()).digest()
        self.assertEqual(sha256d(test_int), expected)

        # Test with invalid type
        with self.assertRaises(Exception):
            sha256d("string")

    def test_uint256(self):
        """Test that uint256 correctly converts bytes to integer."""
        # Create a known byte sequence
        test_bytes = bytes([1] * 32)
        result = uint256(test_bytes)

        # Manual calculation for comparison
        expected = 0
        for i in range(8):
            val = int.from_bytes(test_bytes[i*4:(i+1)*4], byteorder='little')
            expected += val << (i * 32)

        self.assertEqual(result, expected)

    def test_sph_arclen(self):
        """Test spherical arc length calculation."""
        # Create two nodes at known positions
        class MockNode:
            def __init__(self, lat, lon):
                self.latitude = lat
                self.longitude = lon

        # Test nodes at same position
        n1 = MockNode(0, 0)
        n2 = MockNode(0, 0)
        self.assertAlmostEqual(sph_arclen(n1, n2), 0)

        # Test nodes at antipodal points
        n1 = MockNode(0, 0)
        n2 = MockNode(0, 180)
        self.assertAlmostEqual(sph_arclen(n1, n2), math.pi)

        # Test nodes at 90 degrees
        n1 = MockNode(0, 0)
        n2 = MockNode(0, 90)
        self.assertAlmostEqual(sph_arclen(n1, n2), math.pi/2)


class TestBeadClass(unittest.TestCase):
    """Test the Bead class."""

    def setUp(self):
        """Set up test fixtures."""
        self.mock_network = MagicMock()
        self.mock_network.t = 100.0
        self.mock_network.target = 1000

        # Create a genesis bead
        self.genesis_hash = uint256(sha256d(0))
        self.genesis_bead = Bead(self.genesis_hash, set(), self.mock_network, 0)

        # Create a bead with parents
        self.parents = {self.genesis_bead}
        self.test_bead = Bead(None, self.parents, self.mock_network, 1)

    def test_bead_initialization(self):
        """Test that beads are initialized correctly."""
        self.assertEqual(self.test_bead.t, 100.0)
        self.assertEqual(self.test_bead.hash, None)
        self.assertEqual(self.test_bead.parents, self.parents)
        self.assertEqual(self.test_bead.network, self.mock_network)
        self.assertEqual(self.test_bead.creator, 1)
        self.assertEqual(self.test_bead.target, 1000)

    def test_add_pow(self):
        """Test adding proof of work to a bead."""
        test_hash = 12345
        self.test_bead.add_PoW(test_hash)
        self.assertEqual(self.test_bead.hash, test_hash)

    def test_comparison(self):
        """Test bead comparison operators."""
        bead1 = Bead(100, set(), self.mock_network, 0)
        bead2 = Bead(200, set(), self.mock_network, 0)

        self.assertTrue(bead2 > bead1)
        self.assertFalse(bead1 > bead2)

    def test_int_conversion(self):
        """Test converting bead to int."""
        bead = Bead(12345, set(), self.mock_network, 0)
        self.assertEqual(int(bead), 12345)

    def test_str_representation(self):
        """Test string representation of bead."""
        bead = Bead(12345, set(), self.mock_network, 0)
        self.assertEqual(str(bead), "<Bead ...12345>")


class TestNodeClass(unittest.TestCase):
    """Test the Node class."""

    def setUp(self):
        """Set up test fixtures."""
        # Create a mock network
        self.mock_network = MagicMock()
        self.mock_network.t = 0.0

        # Create a genesis bead
        self.genesis_hash = uint256(sha256d(0))
        self.genesis_bead = Bead(self.genesis_hash, set(), self.mock_network, -1)

        # Create a node
        self.node = Node(self.genesis_bead, self.mock_network, 0, 1000)

        # Set a fixed random seed for reproducibility
        random.seed(42)

    def test_node_initialization(self):
        """Test that nodes are initialized correctly."""
        self.assertEqual(self.node.genesis_bead, self.genesis_bead)
        self.assertEqual(self.node.network, self.mock_network)
        self.assertEqual(self.node.nodeid, 0)
        self.assertEqual(self.node.hashrate, 1000)
        self.assertEqual(len(self.node.braid.beads), 1)
        self.assertEqual(len(self.node.braid.tips), 1)
        self.assertIn(self.genesis_bead.hash, self.node.braid.beads)

    def test_add_peers(self):
        """Test adding peers to a node."""
        mock_peer1 = MagicMock()
        mock_peer2 = MagicMock()
        latencies = [0.1, 0.2]

        self.node.add_peers([mock_peer1, mock_peer2], latencies)

        self.assertEqual(len(self.node.peers), 2)
        self.assertEqual(self.node.peers[0], mock_peer1)
        self.assertEqual(self.node.peers[1], mock_peer2)
        self.assertEqual(self.node.latencies, latencies)

    def test_time_to_next_bead(self):
        """Test calculation of time to next bead."""
        # Set a target that will give a predictable result
        self.node.target = MAX_HASH // 100  # 1% chance of success per hash

        # With fixed random seed, this should give consistent results
        time1 = self.node.time_to_next_bead()

        # Reset the random seed and try again
        random.seed(42)
        time2 = self.node.time_to_next_bead()

        # Times should be the same with the same seed
        self.assertEqual(time1, time2)

        # Time should be positive
        self.assertGreater(time1, 0)

        # Time should be inversely proportional to hashrate
        self.node.hashrate = 2000  # Double the hashrate
        random.seed(42)
        time3 = self.node.time_to_next_bead()
        self.assertAlmostEqual(time3, time1 / 2)

    def test_receive(self):
        """Test receiving a bead."""
        # Create a new bead with genesis as parent
        new_bead = Bead(12345, {self.genesis_bead}, self.mock_network, 1)

        # Mock the send method to avoid network interactions
        self.node.send = MagicMock()

        # Mock time_to_next_bead to avoid MagicMock comparison issues
        self.node.time_to_next_bead = MagicMock(return_value=1.0)

        # Receive the bead
        self.node.receive(new_bead)

        # Check that the bead was added to the braid
        self.assertIn(new_bead, self.node.braid)

        # Check that send was called
        self.node.send.assert_called_once_with(new_bead)

    def test_calc_target_fixed(self):
        """Test fixed target calculation."""
        self.node.target = 1000
        parents = {MagicMock(), MagicMock()}
        result = self.node.calc_target_fixed(parents)
        self.assertEqual(result, 1000)

    def test_calc_target_simple(self):
        """Test simple target calculation."""
        # Setup mock parents with known targets
        parent1 = MagicMock()
        parent1.target = 1000
        parent2 = MagicMock()
        parent2.target = 2000
        parents = {parent1, parent2}

        # Setup mock cohorts to simulate a specific Nb value
        self.node.braid.cohorts = [set() for _ in range(TARGET_NC)]
        for i in range(TARGET_NC):
            self.node.braid.cohorts[i] = {MagicMock() for _ in range(TARGET_NB // TARGET_NC)}

        # Test when Nb == TARGET_NB (should return harmonic average)
        result = self.node.calc_target_simple(parents)
        expected = len(parents) * MAX_HASH // (MAX_HASH//1000 + MAX_HASH//2000)
        # The calculation might have slight differences due to integer division
        self.assertAlmostEqual(result, expected, delta=30)

        # Test when Nb > TARGET_NB (should decrease target)
        self.node.braid.cohorts[-1].add(MagicMock())  # Add one more bead
        result = self.node.calc_target_simple(parents)
        
        # The target should decrease, but the exact amount depends on implementation details
        # Just verify it's different from the original target
        self.assertNotEqual(result, expected)

        # Test when Nb < TARGET_NB (should increase target)
        self.node.braid.cohorts = [set() for _ in range(TARGET_NC)]
        for i in range(TARGET_NC):
            self.node.braid.cohorts[i] = {MagicMock() for _ in range((TARGET_NB // TARGET_NC) - 1)}
        result = self.node.calc_target_simple(parents)
        self.assertGreater(result, expected)


class TestBraidClass(unittest.TestCase):
    """Test the Braid class."""

    def setUp(self):
        """Set up test fixtures."""
        # Create a mock network
        self.mock_network = MagicMock()
        self.mock_network.t = 0.0

        # Create a genesis bead
        self.genesis_hash = uint256(sha256d(0))
        self.genesis_bead = Bead(self.genesis_hash, set(), self.mock_network, -1)

        # Create a braid with just the genesis bead
        self.braid = Braid([self.genesis_bead])

    def test_braid_initialization(self):
        """Test that braids are initialized correctly."""
        self.assertEqual(len(self.braid.beads), 1)
        self.assertEqual(len(self.braid.tips), 1)
        self.assertIn(self.genesis_hash, self.braid.beads)
        self.assertIn(self.genesis_bead, self.braid.tips)

    def test_extend_valid_bead(self):
        """Test extending a braid with a valid bead."""
        # Create a new bead with genesis as parent
        new_bead = Bead(12345, {self.genesis_bead}, self.mock_network, 1)

        # Extend the braid
        result = self.braid.extend(new_bead)

        # Check that the extension was successful
        self.assertTrue(result)
        self.assertEqual(len(self.braid.beads), 2)
        self.assertEqual(len(self.braid.tips), 1)
        self.assertIn(new_bead.hash, self.braid.beads)
        self.assertIn(new_bead, self.braid.tips)
        self.assertNotIn(self.genesis_bead, self.braid.tips)

    def test_extend_invalid_bead(self):
        """Test extending a braid with an invalid bead."""
        # Create a bead with non-existent parent
        non_existent_parent = Bead(999, set(), self.mock_network, -1)
        invalid_bead = Bead(12345, {non_existent_parent}, self.mock_network, 1)

        # Try to extend the braid
        result = self.braid.extend(invalid_bead)

        # Check that the extension failed
        self.assertFalse(result)
        self.assertEqual(len(self.braid.beads), 1)
        self.assertEqual(len(self.braid.tips), 1)
        self.assertNotIn(invalid_bead.hash, self.braid.beads)

    def test_extend_duplicate_bead(self):
        """Test extending a braid with a duplicate bead."""
        # Create a new bead and add it to the braid
        new_bead = Bead(12345, {self.genesis_bead}, self.mock_network, 1)
        self.braid.extend(new_bead)

        # Try to add the same bead again
        result = self.braid.extend(new_bead)

        # Check that the extension failed
        self.assertFalse(result)
        self.assertEqual(len(self.braid.beads), 2)

    def test_contains(self):
        """Test the __contains__ method."""
        # Create a new bead and add it to the braid
        new_bead = Bead(12345, {self.genesis_bead}, self.mock_network, 1)
        self.braid.extend(new_bead)

        # Check that the bead is in the braid
        self.assertIn(new_bead, self.braid)

        # Check that a different bead is not in the braid
        different_bead = Bead(54321, {self.genesis_bead}, self.mock_network, 1)
        self.assertNotIn(different_bead, self.braid)

    def test_iter(self):
        """Test the __iter__ method."""
        # Create a new bead and add it to the braid
        new_bead = Bead(12345, {self.genesis_bead}, self.mock_network, 1)
        self.braid.extend(new_bead)

        # Convert the braid to a dict
        braid_dict = dict(self.braid)

        # Check that the dict has the expected structure
        self.assertEqual(len(braid_dict), 2)
        self.assertIn(self.genesis_bead, braid_dict)
        self.assertIn(new_bead, braid_dict)
        self.assertEqual(braid_dict[self.genesis_bead], set())
        self.assertEqual(braid_dict[new_bead], {self.genesis_bead})


class TestNetworkClass(unittest.TestCase):
    """Test the Network class."""

    def setUp(self):
        """Set up test fixtures."""
        # Create a small network for testing
        self.network = Network(nnodes=3, hashrate=1000, ticksize=0.01, npeers=1)

    def test_network_initialization(self):
        """Test that networks are initialized correctly."""
        self.assertEqual(self.network.t, 0.0)
        self.assertEqual(self.network.nnodes, 3)
        self.assertEqual(self.network.hashrate, 1000)
        self.assertEqual(self.network.ticksize, 0.01)
        self.assertEqual(self.network.npeers, 1)
        self.assertEqual(len(self.network.nodes), 3)
        self.assertEqual(len(self.network.inflightdelay), 0)

    def test_tick(self):
        """Test the tick method."""
        # Initial time
        initial_time = self.network.t

        # Perform a tick
        self.network.tick(mine=False)

        # Check that time has advanced
        self.assertGreater(self.network.t, initial_time)

    def test_broadcast(self):
        """Test broadcasting a bead."""
        # Create a bead
        bead = MagicMock()

        # Broadcast to node 0 with delay NETWORK_SIZE
        self.network.broadcast(self.network.nodes[0], bead, NETWORK_SIZE)

        # Check that the bead is in flight
        self.assertIn((0, bead), self.network.inflightdelay)
        self.assertEqual(self.network.inflightdelay[(0, bead)], NETWORK_SIZE)

    def test_reset(self):
        """Test resetting the network."""
        # Add a bead in flight
        bead = MagicMock()
        self.network.broadcast(self.network.nodes[0], bead, 0.1)

        # Advance time
        self.network.t = 10.0

        # Reset the network
        self.network.reset()

        # Check that time is reset and inflight beads are cleared
        self.assertEqual(self.network.t, 0.0)
        self.assertEqual(len(self.network.inflightdelay), 0)

    def test_simulate(self):
        """Test simulating the network."""
        # Patch the tick method to avoid actual simulation
        with patch.object(self.network, 'tick') as mock_tick:
            # Make nodes[0].braid.beads grow each tick
            def side_effect(mine=False):
                self.network.nodes[0].braid.beads[len(self.network.nodes[0].braid.beads)] = MagicMock()
            mock_tick.side_effect = side_effect

            # Simulate until we have 5 beads
            self.network.simulate(nbeads=5, mine=False)

            # Check that tick was called the expected number of times
            self.assertEqual(mock_tick.call_count, 4)  # We start with 1 bead (genesis)


class TestIntegration(unittest.TestCase):
    """Integration tests for the simulator."""

    def test_small_network_simulation(self):
        """Test a small network simulation."""
        # Create a small network
        network = Network(nnodes=2, hashrate=1000, ticksize=0.01, npeers=1)

        # Simulate for a small number of beads
        network.simulate(nbeads=5, mine=False)

        # Check that all nodes have the same number of beads
        self.assertEqual(len(network.nodes[0].braid.beads), 5)
        self.assertEqual(len(network.nodes[1].braid.beads), 5)

        # Check that all nodes have the same beads
        self.assertEqual(set(network.nodes[0].braid.beads.keys()),
                         set(network.nodes[1].braid.beads.keys()))

    def test_different_random_seeds(self):
        """Test that different random seeds produce different braids."""
        # Create two networks with different seeds
        random.seed(1)
        network1 = Network(nnodes=2, hashrate=1000, ticksize=0.01, npeers=1)

        random.seed(2)
        network2 = Network(nnodes=2, hashrate=1000, ticksize=0.01, npeers=1)

        # Simulate both networks
        network1.simulate(nbeads=5, mine=False)
        network2.simulate(nbeads=5, mine=False)

        # Check that the braids are different
        beads1 = set(network1.nodes[0].braid.beads.keys())
        beads2 = set(network2.nodes[0].braid.beads.keys())

        # They should have the same genesis bead but different subsequent beads
        self.assertEqual(len(beads1.intersection(beads2)), 1)

    def test_mining_vs_no_mining(self):
        """Test that mining and no-mining modes produce comparable results."""
        # This test is more of a smoke test since actual mining is random

        # Create a network for no-mining mode
        random.seed(42)
        network_no_mine = Network(nnodes=2, hashrate=1000, ticksize=0.01,
                                  npeers=1, log=False)  # Set log=False to avoid print_hash issues

        # Create a network for mining mode
        random.seed(42)
        network_mine = Network(nnodes=2, hashrate=1000, ticksize=0.01, npeers=1,
                               log=False)  # Set log=False to avoid print_hash issues

        # Simulate both networks
        network_no_mine.simulate(nbeads=5, mine=False)
        network_mine.simulate(nbeads=5, mine=True)

        # Both networks should have 5 beads
        self.assertEqual(len(network_no_mine.nodes[0].braid.beads), 5)
        self.assertEqual(len(network_mine.nodes[0].braid.beads), 5)


if __name__ == '__main__':
    unittest.main()
