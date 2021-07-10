import unittest

import simpy

from topology import Topology


class TestTopology(unittest.TestCase):

    def test_three_node_topology(self):
        env = simpy.Environment()
        result = Topology(env=env)
        self.assertEqual(result.num_nodes, 3)
        self.assertEqual(result.num_neighbours, 2)
        self.assertCountEqual([n.name for n in result.nodes[0].neighbours],
                              ['1', '2'])
        self.assertCountEqual([n.name for n in result.nodes[1].neighbours],
                              ['0', '2'])
        self.assertCountEqual([n.name for n in result.nodes[2].neighbours],
                              ['0', '1'])
