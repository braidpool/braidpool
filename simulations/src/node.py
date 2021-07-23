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

import simpy

from broadcast_pipe import BroadcastPipe
from config import config
from dag import DAG
from message import ShareMessage
from share import Share
from simulation import get_random


class Node:
    prune_depth = 2

    def __init__(self, *, env, name):
        self.seq_no = 0
        self.env = env
        self.name = name
        self.out_pipe = BroadcastPipe(env=env, sender=self.name)
        self.in_pipe = simpy.Store(self.env)
        self.neighbours = set()
        self.dag = DAG()
        # required to help prune dag for large simulations
        self.blocks_received = []
        self.shares_sent = []
        # Track num_shares_sent separately as shares_sent is pruned when block is received
        self.num_shares_sent = 0
        self.shares_not_rewarded = {}
        self.num_blocks = 0

    def heads(self):
        return self.dag.heads()

    def add_neighbour(self, neighbour, reversed=True):
        self.neighbours.add(neighbour)
        self.out_pipe.add_receiver(neighbour.in_pipe)
        if reversed and self not in neighbour.neighbours:
            neighbour.add_neighbour(self)

    def add_neighbours(self, neighbours: list, reversed=True):
        for neighbour in neighbours:
            self.add_neighbour(neighbour, reversed)

    def get_next_share_time(self):
        period = int(config["shares"]["period"])
        if config.getboolean("shares", "randomise"):
            return get_random(period=period)
        else:
            return period

    def generate_shares(self):
        """Process to generate shares at random intervals."""
        block_probability = float(config["shares"]["block_probability"])
        while True:
            # wait for next share
            limit = int(config["shares"]["limit"])
            if limit != -1 and self.seq_no >= limit:
                yield self.env.timeout(int(config["simulation"]["run_time"]))
            else:
                yield self.env.timeout(self.get_next_share_time())

            share = Share(
                source=self.name,
                heads=self.heads(),
                env=self.env,
                seq_no=self.seq_no,
                is_block=get_random(period=1) < block_probability,
            )
            self.seq_no += 1
            if share.is_block:
                self.num_blocks += 1
            msg = ShareMessage(share=share)
            self.add_to_dag(msg.share.hash, msg.share.heads)
            self.send(msg)
            self.shares_sent.append(msg.share.hash)
            self.num_shares_sent += 1
            self.handle_block_found(msg)

    def _log_send(self, msg, forward):
        _type = "s" if not forward else "f"
        if _type == "s":
            logging.info(f"{int(self.env.now)} {_type} n: {self.name} {msg}")
        else:
            logging.debug(f"{int(self.env.now)} {_type} n: {self.name} {msg}")

    def send(self, msg, forward=False):
        self._log_send(msg, forward)
        self.out_pipe.put(msg)

    def receive(self):
        """A process which consumes messages."""
        while True:
            msg = yield self.in_pipe.get()
            logging.info(f"{int(self.env.now)} r n: {self.name} {msg}")
            self.env.process(self.handle_receive(msg.copy()))

    def forward(self, msg):
        msg.decrement_count()
        self.send(msg, forward=True)

    def add_to_dag(self, hash, heads):
        self.dag.add_edges(sources=heads, target=hash)

    def handle_receive(self, msg):
        yield self.env.timeout(int(config["simulation"]["message_processing_time"]))
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
        not_rewarded = self.dag.find_not_reachable(self.shares_sent, msg.share.hash)
        if not_rewarded:
            self.shares_not_rewarded[msg.share.hash] = not_rewarded
        self.blocks_received.append(msg.share.hash)
        self._prune()

    def _prune(self):
        """Prune dag,  blocks_received and shares_sent up to last two blocks received"""
        if len(self.blocks_received) <= self.prune_depth:
            return
        prune_upto = self.blocks_received[-self.prune_depth :][0]
        pruned_hashes = self.dag.prune_upto(prune_upto)
        del self.blocks_received[: -self.prune_depth]
        self._prune_shares_sent(pruned_hashes)

    def _prune_shares_sent(self, pruned_hashes):
        # Possible improvement - the implementation here goes over shares_sent twice.
        for hash in pruned_hashes:
            if hash in self.shares_sent:
                self.shares_sent.remove(hash)

    def start(self):
        logging.info(f"{self.name} starting...")
        self.env.process(self.receive())
        self.env.process(self.generate_shares())
