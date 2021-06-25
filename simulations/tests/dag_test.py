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
