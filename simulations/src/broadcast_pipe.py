import logging

from config import config


class BroadcastPipe(object):
    """A Broadcast pipe that allows one process to send messages to many.

    Each node has a broadcast pipe and it's neighbours are added to
    the pipe using Topology
    """

    def __init__(self, *, env, sender, latency=None):
        self.env = env
        self.sender = sender
        self.pipes = []
        self.latency = latency if latency else int(config['p2p']['latency'])

    def _add_latency(self, pipe, value):
        logging.debug(f'Put on {self.sender} {value.share.hash} at '
                      f'{self.env.now + self.latency}')
        yield self.env.timeout(self.latency)
        logging.debug(f'{self.sender} putting: {value} items:  '
                      f'{self.pipes_items()}')
        pipe.put(value)
        logging.debug(f'{self.sender} put done: {value} '
                      f'items: {self.pipes_items()}')

    def put(self, value):
        """Broadcast a *value* to all receivers."""
        if self.pipes:
            events = [self.env.process(self._add_latency(pipe, value))
                      for pipe in self.pipes]
            return self.env.all_of(events)  # Condition event for all "events"

    def add_receiver(self, receiver):
        self.pipes.append(receiver)

    def pipes_items(self):
        res = ''
        for pipe in self.pipes:
            res += ', '.join([item.share.hash for item in pipe.items])
        return res
