from collections import defaultdict


class DAG:
    def __init__(self):
        self.adj_matrix = defaultdict(list)

    def targets(self, source):
        return self.adj_matrix[source]

    def add_edge(self, source, target):
        return self.adj_matrix[source].append(target)

    def heads(self):
        '''
        Return shares that don't have any out edges.
        Non optimised implementation for now.
        '''
        return [source for source, adj_matrix in self.adj_matrix.items()
                if len(adj_matrix) == 0]
