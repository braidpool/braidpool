import unittest

from dag import DAG


class TestDAG(unittest.TestCase):
    def test_add_edge(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        self.assertCountEqual(dag.heads(), ['a'])
        self.assertTrue(dag.has('a'))
        self.assertTrue(dag.has('b'))
        self.assertTrue(dag.has('c'))
        self.assertFalse(dag.has('d'))
        self.assertTrue(dag.has_path('b', 'a'))
        self.assertFalse(dag.has_path('a', 'b'))

    def test_find_not_reachable_with_all_reachable(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        self.assertCountEqual(dag.find_not_reachable(['b', 'c'], 'a'), [])

    def test_find_not_reachable_with_none_reachable(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['d'], target='e')
        self.assertCountEqual(dag.find_not_reachable(['d', 'e'], 'a'),
                              ['d', 'e'])

    def test_find_not_reachable_with_some_reachable(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['d'], target='e')
        self.assertCountEqual(dag.find_not_reachable(['b', 'c', 'd', 'e'], 'a'),
                              ['d', 'e'])

    def test_find_not_reachable_with_some_reachable_reversed_order(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['d'], target='e')
        # The first argument is the shares sent by a node. They are send in the
        # order d, e, b, c. We assume that if there is a path from c to a,
        # then there is a path as d -> e -> b -> c, and therefore return empty
        # list
        self.assertCountEqual(dag.find_not_reachable(['d', 'e', 'b', 'c'], 'a'),
                              [])

    def test_prune_dag_should_remove_nodes_preceding_given_node(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['a'], target='d')
        dag.add_edges(sources=['d'], target='e')
        self.assertCountEqual(['c', 'b', 'a', 'd', 'e'], dag.to_string())

        dag.prune_upto('d')
        self.assertCountEqual(['d', 'e'], dag.to_string())
