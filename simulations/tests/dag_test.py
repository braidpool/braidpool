from dag import DAG


class TestDAG():
    def test_add_edge(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        assert dag.heads() == ['a']
        assert dag.has('a')
        assert dag.has('b')
        assert dag.has('c')
        assert not dag.has('d')
        assert dag.has_path('b', 'a')
        assert not dag.has_path('a', 'b')

    def test_find_not_reachable_with_all_reachable(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        print(dag.to_string())
        assert dag.find_not_reachable(['b', 'c'], 'a') == []

    def test_find_not_reachable_with_none_reachable(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['d'], target='e')
        print(dag.to_string())
        assert dag.find_not_reachable(['d', 'e'], 'a') == ['d', 'e']

    def test_find_not_reachable_with_some_reachable(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['d'], target='e')
        print(dag.to_string())
        assert dag.find_not_reachable(['b', 'c', 'd', 'e'], 'a') == ['d', 'e']

    def test_find_not_reachable_with_some_reachable_reversed_order(self):
        dag = DAG()
        dag.add_edges(sources=['b', 'c'], target='a')
        dag.add_edges(sources=['d'], target='e')
        print(dag.to_string())
        # The first argument is the shares sent by a node. They are send in the
        # order d, e, b, c. We assume that if there is a path from c to a,
        # then there is a path as d -> e -> b -> c, and therefore return empty
        # list
        assert dag.find_not_reachable(['d', 'e', 'b', 'c'], 'a') == []
