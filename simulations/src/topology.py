import math
from collections import namedtuple

import networkx as nx

from node import Node

NodeLatency = namedtuple("NodeLatency", ["node", "latency"])


class Topology:
    """
    Create nodes and relationships between nodes and decides latencies
    between them.
    node_neighbours stores node -> [NodeLatency]
    """

    def __init__(self, *, env, num_nodes=3, mean_latency=300, num_neighbours=8):
        self.env = env
        self.nodes = {}
        self.num_nodes = num_nodes
        self.num_neighbours = min(num_neighbours, self.num_nodes - 1)
        self._create_nodes()
        self._setup_neighbours()

    def _create_nodes(self):
        for i in range(0, self.num_nodes):
            node = Node(name=i, env=self.env)
            self.nodes[node.name] = node

    def _setup_neighbours(self):
        graph = nx.random_regular_graph(self.num_neighbours, self.num_nodes)
        for node in graph.nodes():
            neighbours = [
                self.nodes[neighbour] for neighbour in nx.neighbors(graph, node)
            ]
            self.nodes[node].add_neighbours(neighbours, reversed=False)

    def neighbours_of(self, node):
        """Return [node_latency] for all nodes that are neighbours of node"""
        return self.node_neighbours[node]

    def latency_between(self, node_a, node_b):
        """Return latency from node_a to node_b if node_b is a neighbour"""
        if node_b in self.node_neighbours[node_a]:
            return self.node_neighbours[node_a].latency
        return math.inf
