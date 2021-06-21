from collections import namedtuple
from math import inf

NodeLatency = namedtuple('NodeLatency', ['node', 'latency'])


class Topology():
    """
    Determine relationships between nodes and decides latencies between them

    node_neighbours stores node -> [NodeLatency]
    """

    def __init__(self):
        self.node_neighbours = {}

    def neighbours(self, node):
        ''' Return [node_latency] for all nodes that are neighbours of node'''
        return self.node_neighbours[node]

    def latency(self, node_a, node_b):
        ''' Return latency from node_a to node_b if node_b is a neighbour'''
        if node_b in self.node_neighbours[node_a]:
            return self.node_neighbours[node_a].latency
        return inf
