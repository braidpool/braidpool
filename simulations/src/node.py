"""Peer to Peer Communication

- Composed of Nodes

- Each Node is connected bi-directionally to N neighbours (Defined by
  Topology)

- Node generates a share every T seconds

- There is a different delay from a Node to all its
  neighbours. (Defined by Topology)

Based on:
https://simpy.readthedocs.io/en/latest/examples/process_communication.html
"""
import logging
import random

import simpy

from broadcast_pipe import BroadcastPipe
from config import config
from dag import DAG
from message import ShareMessage
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
        self.shares_sent = []
        self.shares_not_rewarded = {}

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

    def add_neighbours(self, neighbours: list):
        for neighbour in neighbours:
            self.add_neighbour(neighbour)

    def get_next_share_time(self):
        period = int(config['shares']['period'])
        if config.getboolean('shares', 'randomise'):
            return random.randint(0, period - 1)
        else:
            return period

    def generate_shares(self):
        """Process to generate shares at random intervals."""
        block_probability = float(config['shares']['block_probability'])
        while True:
            # wait for next share
            limit = int(config['shares']['limit'])
            if limit != -1 and self.seq_no >= limit:
                yield self.env.timeout(int(config['simulation']['run_time']))
            else:
                yield self.env.timeout(self.get_next_share_time())

            share = Share(source=self.name, heads=self.heads(), env=self.env,
                          seq_no=self.seq_no,
                          is_block=random.random() < block_probability)
            self.seq_no += 1
            msg = ShareMessage(share=share)
            self.add_to_dag(msg.share.hash, msg.share.heads)
            self.send(msg)
            self.shares_sent.append(msg.share.hash)
            self.handle_block_found(msg)

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

    def add_to_dag(self, hash, heads):
        self.dag.add_edges(sources=heads, target=hash)

    def handle_receive(self, msg):
        while True:
            yield self.env.timeout(self.message_processing_time(msg))
            msg_in_dag = self.dag.has(msg.share.hash)
            if not msg_in_dag:
                if msg.should_forward():
                    self.forward(msg)
                self.add_to_dag(msg.share.hash, msg.share.heads)
                self.handle_received_block_found(msg)

    def handle_received_block_found(self, msg):
        if not msg.share.is_block:
            return
        if msg.share.source == self.name:
            return
        self.handle_block_found(msg)

    def handle_block_found(self, msg):
        # find delta between latest share this node already sent and
        # the last one referenced in the receieved share.
        not_rewarded = self.dag.find_not_reachable(self.shares_sent,
                                                   msg.share.hash)
        if not_rewarded:
            self.shares_not_rewarded[msg.share.hash] = not_rewarded

    def start(self):
        logging.info(f'{self.name} starting...')
        self.env.process(self.receive())
        self.env.process(self.generate_shares())
