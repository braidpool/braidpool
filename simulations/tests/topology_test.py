import unittest

import simpy

from topology import Topology


class TestTopology(unittest.TestCase):
    def test_three_node_topology(self):
        env = simpy.Environment()
        result = Topology(env=env)
        self.assertEqual(result.num_nodes, 3)
        self.assertEqual(result.num_neighbours, 2)
        self.assertCountEqual(
            [n.name for n in result.nodes[0].neighbours], [1, 2]
        )
        self.assertCountEqual(
            [n.name for n in result.nodes[1].neighbours], [0, 2]
        )
        self.assertCountEqual(
            [n.name for n in result.nodes[2].neighbours], [0, 1]
        )

    def test_large_node_topology(self):
        env = simpy.Environment()
        result = Topology(env=env, num_nodes=1000, num_neighbours=8)
        self.assertEqual(result.num_nodes, 1000)
        self.assertEqual(result.num_neighbours, 8)
        for node in result.nodes.values():
            self.assertEqual(len(node.neighbours), 8)
