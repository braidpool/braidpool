from collections import defaultdict


class DAG:
    def __init__(self):
        self.adj_list = defaultdict(set)

    def add_nodes(self, targets):
        for target in targets:
            if target not in self.adj_list:
                self.adj_list[target] = set()

    def targets(self, source):
        return self.adj_list[source]

    def add_edges(self, *, sources, target):
        for source in sources:
            self.adj_list[source].add(target)
        self.add_nodes([target])

    def heads(self):
        '''
        Return shares that don't have any out edges.
        Non optimised implementation for now.
        '''
        return [source for source, adj_list in self.adj_list.items()
                if len(adj_list) == 0]

    def has(self, hash):
        return hash in self.adj_list

    def __repr__(self):
        formatted = ''
        for key, values in self.adj_list.items():
            print(key)
            formatted + f'{key}:\n'
            for value in values:
                print(f'\t\t{value}')
                formatted + f'\t\t{value}'
        return formatted
