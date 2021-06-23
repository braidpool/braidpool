from config import config
import simpy

class BroadcastPipe(object):
    """A Broadcast pipe that allows one process to send messages to many.

    Each node has a broadcast pipe and it;s neighbours are added to
    the pipe using Topology

    """

    def __init__(self, env, capacity=simpy.core.Infinity,
                 latency=None):
        self.env = env
        self.capacity = capacity
        self.pipes = []
        self.latency = latency if latency else int(config['p2p']['latency'])

    def _add_latency(self, pipe, value):
        yield self.env.timeout(self.latency)
        pipe.put(value)

    def put(self, value):
        """Broadcast a *value* to all receivers."""
        if self.pipes:
            events = [self.env.process(self._add_latency(pipe, value))
                      for pipe in self.pipes]
            return self.env.all_of(events)  # Condition event for all "events"

    def get_output_conn(self):
        """Get a new output connection for this broadcast pipe.

        The return value is a :class:`~simpy.resources.store.Store`.

        """
        pipe = simpy.Store(self.env, capacity=self.capacity)
        self.pipes.append(pipe)
        return pipe
