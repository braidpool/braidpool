import networkx as nx


class DAG(nx.DiGraph):
    def __init__(self):
        super().__init__()

    def add_edges(self, *, sources, target):
        for source in sources:
            self.add_edge(source, target)
        self.add_node(target)

    def heads(self):
        '''
        Return shares that don't have any out edges.
        Non optimised implementation for now.
        '''
        return [node for node in self.nodes() if self.out_degree(node) == 0]

    def has(self, hash):
        return hash in self

    def has_path(self, a, b):
        return nx.has_path(self, a, b)

    def to_string(self):
        return list(nx.topological_sort(self))
