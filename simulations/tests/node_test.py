import unittest

import simpy

from dag import DAG
from node import Node


class TestNode(unittest.TestCase):
    def test_prune_should_remove_nodes_preceding_given_hash(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['a'], target='d')
        dag.add_edges(sources=['d'], target='e')

        env = simpy.Environment()
        node = Node(env=env, name='node 1')
        node.dag = dag
        node.blocks_received = ['c', 'b', 'a', 'd', 'e']

        self.assertCountEqual(['c', 'b', 'a', 'd', 'e'], dag.to_string())
        node._prune()
        self.assertCountEqual(['d', 'e'], node.dag.to_string())
