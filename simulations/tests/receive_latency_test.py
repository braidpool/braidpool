import unittest

from post_process.receive_latency import ReceiveLatency


class TestReceiveLatency(unittest.TestCase):
    def test_process_four_nodes(self):
        processor = ReceiveLatency()
        processor.run('tests/fixtures/log_4_nodes.log')
        self.assertTrue(processor.get_average_latencies()['1-412'], 500)
        self.assertTrue(processor.get_average_latency(), 500)
