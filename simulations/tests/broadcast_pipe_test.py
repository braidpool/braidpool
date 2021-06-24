import simpy

from broadcast_pipe import BroadcastPipe


class TestBroadcastPipe():

    def receive_from_fifo_pipe(self, env, pipe):
        last_received = 0
        while True:
            msg = yield env.process(pipe.get())
            assert msg == last_received + 1
            last_received += 1

    def test_broadcast_pipe_is_fifo(self):
        env = simpy.Environment()
        pipe = BroadcastPipe(env=env, sender='test')
        pipe.put(1)
        pipe.put(2)
        pipe.put(3)
        self.receive_from_fifo_pipe(env, pipe)
