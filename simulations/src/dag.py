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

    def find_not_reachable(self, share_hashes, block_hash):
        '''
        Find the nodes in the graph that are in share_hashes but not
        reachable from block_hash
        TODO: Optimise this.
        '''
        collected = []
        for share_hash in reversed(share_hashes):
            if not self.has_path(share_hash, block_hash):
                collected.append(share_hash)
            else:
                break
        return list(reversed(collected))

    def to_string(self):
        return list(nx.topological_sort(self))

    def prune_upto(self, upto):
        '''Deletes all nodes from graph that precede upto. Does not remove upto'''
        for node in nx.topological_sort(self):
            if node == upto:
                return
            self.remove_node(node)
