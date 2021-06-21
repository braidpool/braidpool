"""Peer to Peer Communication

- Composed of Nodes

- Each Node is connected bi-directionally to N neighbours (Defined by
  Topology)

- Node generates a share every T seconds

- There is a different delay from a Node to all its
  neighbours. (Defined by Topology)

Based on: https://simpy.readthedocs.io/en/latest/examples/process_communication.html
"""
import random

import simpy

from broadcast_pipe import BroadcastPipe
from dag import DAG
from share import Share

SHARE_PERIOD = 1000
MESSAGE_PROCESSING_TIME = 10


class Node:
    def __init__(self, *, env, name):
        self.env = env
        self.name = name
        self.out_pipe = BroadcastPipe(env)
        dummy_in_pipe = simpy.Store(self.env)
        self.in_pipes = [dummy_in_pipe]
        self.neighbours = []
        self.dag = DAG()

    def heads(self):
        return self.dag.heads()

    def message_processing_time(self, msg):
        """
        Return time taken to process a receieved message
        For now return constant time.
        """
        return MESSAGE_PROCESSING_TIME

    def add_neighbour(self, neighbour):
        self.neighbours.append(neighbour)
        pipe_output_conn = self.out_pipe.get_output_conn()
        neighbour.add_in_pipe(pipe_output_conn)

    def add_in_pipe(self, pipe):
        self.in_pipes.append(pipe)

    def send(self):
        """Process to generate shares at random intervals."""
        while True:
            # wait for next share
            yield self.env.timeout(random.randint(0, SHARE_PERIOD - 1))

            # messages are time stamped to later check if the consumer was
            # late getting them.  Note, using event.triggered to do this may
            # result in failure due to FIFO nature of simulation yields.
            # (i.e. if at the same env.now, message_generator puts a message
            # in the pipe first and then message_consumer gets from pipe,
            # the event.triggered will be True in the other order it will be
            # False
            msg = Share(source=self.name, heads=self.heads(), env=self.env)
            print(f's e: {self.env.now} n: {self.name} {msg}')
            self.out_pipe.put(msg)

    def receive(self):
        """A process which consumes messages."""
        while True:
            received_messages = yield self.env.any_of([pipe.get() for pipe
                                                       in self.in_pipes])

            for _, msg in received_messages.items():
                print(f'r e: {self.env.now} n: {self.name} {msg}')
                yield self.env.timeout(self.message_processing_time(msg))

    def start(self):
        print(f'{self.name} starting...')
        self.env.process(self.receive())
        self.env.process(self.send())
