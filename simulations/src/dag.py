from collections import defaultdict


class DAG:
    def __init__(self):
        self.adj_list = defaultdict(list)

    def add_nodes(self, targets):
        for target in targets:
            if target not in self.adj_list:
                self.adj_list[target] = []

    def targets(self, source):
        return self.adj_list[source]

    def add_edges(self, source, targets):
        self.adj_list[source].extend(targets)
        self.add_nodes(targets)

    def heads(self):
        '''
        Return shares that don't have any out edges.
        Non optimised implementation for now.
        '''
        print(self.adj_list)
        return [source for source, adj_list in self.adj_list.items()
                if len(adj_list) == 0]

    def has(self, hash):
        return hash in self.adj_list
