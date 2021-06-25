"""Peer to Peer Communication

- Composed of Nodes

- Each Node is connected bi-directionally to N neighbours (Defined by
  Topology)

- Node generates a share every T seconds

- There is a different delay from a Node to all its
  neighbours. (Defined by Topology)

Based on: https://simpy.readthedocs.io/en/latest/examples/process_communication.html
"""
import logging
import random

import simpy

from broadcast_pipe import BroadcastPipe
from config import config
from dag import DAG
from message import Message
from share import Share

MESSAGE_PROCESSING_TIME = 10


class Node:
    def __init__(self, *, env, name):
        self.seq_no = 0
        self.env = env
        self.name = name
        self.out_pipe = BroadcastPipe(env=env, sender=self.name)
        self.in_pipe = simpy.Store(self.env)
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
        self.out_pipe.add_receiver(neighbour.in_pipe)

    def get_next_share_time(self):
        period = int(config['shares']['period'])
        if config.getboolean('shares', 'randomise'):
            return random.randint(0, period - 1)
        else:
            return period

    def generate_shares(self):
        """Process to generate shares at random intervals."""
        while True:
            # wait for next share
            limit = int(config['shares']['limit'])
            if limit != -1 and self.seq_no >= limit:
                yield self.env.timeout(int(config['simulation']['run_time']))
            else:
                yield self.env.timeout(self.get_next_share_time())

            # messages are time stamped to later check if the consumer was
            # late getting them.  Note, using event.triggered to do this may
            # result in failure due to FIFO nature of simulation yields.
            # (i.e. if at the same env.now, message_generator puts a message
            # in the pipe first and then message_consumer gets from pipe,
            # the event.triggered will be True in the other order it will be
            # False
            share = Share(source=self.name, heads=self.heads(), env=self.env,
                          seq_no=self.seq_no)
            self.seq_no += 1
            msg = Message(share=share)
            self.add_to_dag(msg)
            self.send(msg)

    def send(self, msg, forward=False):
        _type = 's' if not forward else 'f'
        logging.info(f'{_type} e: {self.env.now} n: {self.name} {msg}')
        self.out_pipe.put(msg)

    def receive(self):
        """A process which consumes messages."""
        while True:
            msg = yield self.in_pipe.get()
            logging.info(f'r e: {self.env.now} n: {self.name} {msg}')
            self.env.process(self.handle_receive(msg))

    def forward(self, msg):
        msg.decrement_count()
        self.send(msg, forward=True)

    def should_forward(self, msg):
        return msg.should_forward() and not self.dag.has(msg.share.hash)

    def add_to_dag(self, msg):
        self.dag.add_edges(sources=msg.share.heads, target=msg.share.hash)

    def handle_receive(self, msg):
        while True:
            yield self.env.timeout(self.message_processing_time(msg))
            # If receieved first time insert into dag
            if self.should_forward(msg):
                self.forward(msg)
            # add to dag after should_forward check has been carried out
            self.add_to_dag(msg)
            # check counter and if required send again
            # detect any missing shares and send request for receiving missing shares

    def start(self):
        logging.info(f'{self.name} starting...')
        self.env.process(self.receive())
        self.env.process(self.generate_shares())
