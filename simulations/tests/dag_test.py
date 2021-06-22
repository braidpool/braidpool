from dag import DAG


class TestDAG():
    def test_add_edge(self):
        dag = DAG()
        dag.add_edges('a', ['b', 'c'])
        assert dag.heads() == ['b', 'c']
        assert dag.has('a')
        assert dag.has('b')
        assert dag.has('c')
        assert not dag.has('d')
