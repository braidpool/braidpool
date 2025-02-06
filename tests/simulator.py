#!/usr/bin/env python3

# Braidpool Simulator

# This code simulates a network of nodes distributed on a sphere (the Earth)
# with realistic latency defined by the path length between them on the surface
# of the sphere. Note that all signals are assumed to propagate at the speed
# of light -- propagation speed in copper or global fiber optics is not simulated.

# FIXME give numbers for network and per-node hashrate

from argparse import ArgumentParser, BooleanOptionalAction
from copy import copy
from math import pi, sqrt, sin, cos, acos, log
from random import randint, random, sample
import braid, hashlib, struct, sys, time

NETWORK_SIZE     = 0.06676  # The round-trip time in seconds to traverse the network = pi*r_e/c
TICKSIZE         = 0.001    # One "tick" of the network in which beads will be propagated and mined
MAX_HASH         = 2**256-1 # Maximum value a 256 bit unsigned hash can have, used to calculate targets
NETWORK_HASHRATE = 800000   # Single core hashrate in hashes/s (run this script with -B)
OVERHEAD_FUDGE   = 3        # Fudge factor for processing overhead compared to sha256d mining

def Hash(msg: bytes):
    """(SHA256^2)(msg) -> bytes"""
    if type(msg) == bytes:
        return hashlib.sha256(hashlib.sha256(msg).digest()).digest()
    elif type(msg) == int:
        return hashlib.sha256(hashlib.sha256(msg.to_bytes(32, byteorder='big')).digest()).digest()
    else:
        raise Exception("Unknown type to hash: ", type(msg))

def sph_arclen(n1, n2):
    """ Compute the arc length on the surface of a unit sphere. """
    # phi = 90 - latitude
    phi1 = (90.0 - n1.latitude)*pi/180.0
    phi2 = (90.0 - n2.latitude)*pi/180.0

    # theta = longitude
    theta1 = n1.longitude*pi/180.0
    theta2 = n2.longitude*pi/180.0

    c = sin(phi1)*sin(phi2)*cos(theta1-theta2) + cos(phi1)*cos(phi2)
    return acos(c)

# Convert a string to a uint256 instead of importing python-bitcoinlib
def uint256(s):
    """Convert bytes to uint256"""
    r = 0
    t = struct.unpack(b"<IIIIIIII", s[:32])
    for i in range(8):
        r += t[i] << (i * 32)
    return r

# Define the geometric distribution instead of importing numpy
def geometric(p):
    """
    Sample from the geometric distribution with success probability p.
    Returns the number of trials until the first success (k ≥ 1).

    Reference:
    - Weisstein, Eric W. "Geometric Distribution." MathWorld--A Wolfram Web Resource.
      http://mathworld.wolfram.com/GeometricDistribution.html
    """
    if not (0 < p < 1):
        raise ValueError("p must be in the open interval (0, 1)")
    if p < 1e-6:
        return int(log(1 - random()) / -(p+p**2/2+p**3/3+p**4/4+p**5/5)) + 1
    else:
        return int(log(1 - random()) / log(1 - p)) + 1

class Network:
    """ Abstraction for an entire network containing <n> nodes.  The network has
        a internal clock for simulation which uses <ticksize>.  Latencies are taken
        from a uniform distribution on [0,1) so <ticksize> should be < 1.
    """
    def __init__(self, nnodes, ticksize=TICKSIZE, npeers=4, target=None, topology='sphere'):
        self.t                      = 0                 # the current "time"
        self.ticksize               = ticksize          # the size of a "tick": self.t += self.tick at each step
        self.npeers                 = npeers
        self.nnodes                 = nnodes
        self.genesis                = uint256(Hash(0))
        self.beads                  = {}                # a hash map of all beads in existence
        self.beads[self.genesis]    = Bead(self.genesis, set(), self, -1)
        self.nodes                  = [Node(self.genesis, self, nodeid,
                                            initial_target=target) for nodeid in
                                       range(nnodes)]
        latencies                   = None
        for (node, peers) in zip(self.nodes, [sample(list(set(range(nnodes)) - {me}),  \
                npeers) for me in range(nnodes)]):
            if topology == 'sphere':
                latencies = [10*sph_arclen(node, self.nodes[i]) for i in peers];
            node.setpeers([self.nodes[i] for i in peers], latencies)
        self.reset(target=target)

    def tick(self, mine=True):
        """ Execute one tick. """
        self.t += self.ticksize

        # Have each node attempt to mine a bead
        if mine:
            for node in self.nodes:
                node.tick(mine=True)
        else:
            # next bead will be generated
            next_bead_dt = min(self.nodes, key=lambda n:n.tremaining).tremaining
            # next bead is received by a node after latency
            next_bead_dt = min(next_bead_dt, min(self.inflightdelay.values())) if self.inflightdelay else next_bead_dt
            for n in self.nodes:
                n.tremaining -= next_bead_dt
                n.tick(mine=False)

        for (node, bead) in copy(self.inflightdelay):
            if mine:
                self.inflightdelay[(node, bead)] -= self.ticksize
            else:
                self.inflightdelay[(node, bead)] -= next_bead_dt
            if self.inflightdelay[(node, bead)] <= 0:
                node.receive(bead)
                del self.inflightdelay[(node, bead)]

    def simulate(self, nbeads=20, mine=False):
        """ Simulate the network until we have <nbeads> beads """
        while len(self.nodes[0].braid.beads) < nbeads:
            self.tick(mine=mine)

    def broadcast(self, node, bead, delay):
        """ Announce a block/bead discovery to a node who is <delay> away. """
        if bead not in node.beads:
            prevdelay = NETWORK_SIZE
            if (node,bead) in self.inflightdelay:
                prevdelay = self.inflightdelay[(node, bead)]
            self.inflightdelay[(node, bead)] = min(prevdelay, delay)

    def reset(self, target=None):
        self.t = 0
        self.beads = {}
        self.beads[self.genesis] = Bead(self.genesis, set(), self, -1)
        self.inflightdelay = {}
        for node in self.nodes:
            node.reset(target)

    def printinflightdelays(self):
        for (node, bead) in self.inflightdelay:
            print("bead ", bead, " to node ", node, " will arrive in %fs"%self.inflightdelay[(node, bead)])

class Node:
    """ Abstraction for a node. """
    def __init__(self, genesis, network, nodeid, initial_target=None):
        self.genesis    = genesis
        self.network    = network
        self.peers      = []
        self.latencies  = []
        self.nodeid     = nodeid
        # A salt for this node, so all nodes don't produce the same hashes
        self.nodesalt   = uint256(Hash(randint(0,MAX_HASH)))
        self.nonce      = 0         # Will be increased in the mining process
        self.tremaining = None      # Ticks remaining before this node produces a bead
        self.reset(initial_target)
        # Geospatial location information
        self.latitude   = pi*(1/2-random())
        self.longitude  = 2*pi*random()

    def reset(self, initial_target=None):
        self.beads      = [self.network.beads[self.network.genesis]] # A list of beads in the order received
        self.braid      = Braid(self.beads)
        self.incoming   = set()                                      # incoming beads we were unable to process
        self.target     = initial_target
        self.braid.tips = {self.beads[0]}
        self.tremaining = geometric(self.target/MAX_HASH)

    def __str__(self):
        return "<Node %d>"%self.nodeid

    def setpeers(self, peers, latencies=None):
        """ Add a peer separated by a latency <delay>. """
        self.peers = peers
        if latencies: self.latencies = latencies
        else:         self.latencies = sample(len(peers))*NETWORK_SIZE
        assert(len(self.peers) == len(self.latencies))

    def tick(self, mine=True):
        """ Add a Bead satisfying <target>. """
        # First try to extend all braids by received beads that have not been added to a braid
        oldtips = self.braid.tips
        self.process_incoming()
        b = Bead(None, copy(self.braid.tips), self.network, self.nodeid)
        if mine:
            PoW = uint256(Hash(self.nodesalt+self.nonce))
            self.nonce += 1
            if PoW < self.target:
                b.addPoW(PoW)
                self.receive(b)     # Send it to myself (will rebroadcast to peers)
        else :
            b = Bead(None, copy(self.braid.tips), self.network, self.nodeid)
            if(self.tremaining <= 0):
                PoW = (uint256(Hash(self.nodesalt+self.nonce))*self.target)//MAX_HASH
                self.nonce += 1
                b.addPoW(PoW)
                # The expectation of how long it will take to mine a block is Geometric
                # This node will generate one after this many hashing rounds (ticks)
                self.receive(b)     # Send it to myself (will rebroadcast to peers)
                # How many ticks before this node generate a bead again
                self.tremaining = geometric(self.target/MAX_HASH)
            elif(self.braid.tips != oldtips):
                # reset mining if we have new tips
                self.tremaining = geometric(self.target/MAX_HASH)

    def receive(self, bead):
        """ Recieve announcement of a new bead. """
        if bead in self.beads: return
        else: self.beads.append(bead)
        if not self.braid.extend(bead): # We don't have parents for this bead
            self.incoming.add(bead)
        self.process_incoming()
        self.send(bead)

    def process_incoming(self):
        """ Process any beads in self.incoming that have not yet been added. """
        while True:
            oldincoming = copy(self.incoming)
            for bead in oldincoming:
                if self.braid.extend(bead): self.incoming.remove(bead)
            if oldincoming == self.incoming:
                break

    def send(self, bead):
        """ Announce a new block from a peer to this node. """
        for (peer, delay) in zip(self.peers, self.latencies):
            self.network.broadcast(peer, bead, delay)

class Bead:
    """ A bead is either a block of transactions, or an individual transaction.
        This class stores auxiliary information about a bead and is separate
        from the vertex being stored by the Braid class.  Beads are stored by
        the Braid object in the same order as vertices.  So if you know the
        vertex v, the Bead instance is Braid.beads[int(v)].  graph_tool vertices
        can be cast to integers as int(v), giving their index.
    """

    def __init__(self, hash, parents, network, creator):
        """ All attributes of this object should be serializable on the network
            and not refer to internal data structures. """
        self.t = network.t
        self.hash = hash    # a hash that identifies this block
        self.parents = parents
        self.children = set() # filled in by Braid.make_children()
        self.siblings = set() # filled in by Braid.analyze
        self.cohort = set() # filled in by Braid.analyze
        self.network = network
        self.creator = creator
        if creator != -1: # if we're not the genesis block (which has no creator node)
            self.difficulty = MAX_HASH//network.nodes[creator].target
        else: self.difficulty = 1
        self.sibling_difficulty = 0
        if hash is not None:
            network.beads[hash] = self # add myself to global list
        self.reward = None  # this bead's reward (filled in by Braid.rewards)

    def __str__(self):
        return "<Bead ...%04d>"%(self.hash%10000)

    def addPoW(self, hash):
        self.hash = hash
        self.network.beads[hash] = self

    def parent_target(self):
        """ Compute the average target of its parents.  """
        # Average parent difficulty
        w_1 = sum([p.difficulty for p in self.parents])//len(self.parents)
        # Average parent target (maximum value a hash can have)
        return MAX_HASH//w_1

class Braid:
    """ A Braid is a Directed Acyclic Graph with no incest (parents may not also
        be non-parent ancestors).  A braid may have multiple tips. """

    def __init__(self, beads=[], filename=None):
        self.beads    = []                          # A list of beads in this braid
        self.times    = {}                          # Time of arrival for each bead
        self.vhashes  = {}                          # A dict of (hash, Bead) for each bead
        self.tips     = set()                       # A tip is a bead with no children.

        if beads:
            for b in beads:
                self.beads.append(b)
                self.tips.add(b)
                self.vhashes[b.hash]   = b
                for p in b.parents:
                    self.times[b.hash] = b.t
                    if p in self.tips:
                        self.tips.remove(p)
        elif filename:
            print("FIXME loading from a file unimplemened.")

    def __iter__(self):
        """ You can dump a representation of a braid as a python dictionary like:
            dict(b), which uses this iterator. This gives integer indices for
            the beads (instead of hashes) suitable for test cases.
        """
        for b in self.beads:
            yield self.beads.index(b), {self.beads.index(p) for p in b.parents}

    def extend(self, bead):
        """ Add a bead to the end of this braid. Returns True if the bead
            successfully extended this braid, and False otherwise. """
        if (not bead.parents                                                # No parents -- bad block
                or not all([p.hash in self.vhashes for p in bead.parents])  # We don't have all parents
                or bead in self.beads):                                     # We've already seen this bead
            return False
        self.beads.append(bead)
        self.vhashes[bead.hash]   = bead
        for p in bead.parents:
            self.times[bead.hash] = bead.t
            if p in self.tips:
                self.tips.remove(p)
        self.tips.add(bead)
        return True

if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("-o", "--output-file", dest="filename",
        help="Filename to which we will write the generated braid",
        default="braid.json")
    parser.add_argument("-n", "--nodes",
        help="Number of nodes to simulate",
        default=25)
    parser.add_argument("--mine", action=BooleanOptionalAction,
        help="Do sha256d mining (if --no-mine we will use a geometric distribution)",
        default = False)
    parser.add_argument("-t", "--target",
        help="Target difficulty exponent t where T=2**t-1",
        default=244)
    parser.add_argument("-b", "--beads",
        help="Number of beads to simulate",
        default=50)
    parser.add_argument("-p", "--peers",
        help="Number of peers per node",
        default=4)
    parser.add_argument("-d", "--description",
        help="String description describing this simulation run",
        default="No description provided")
    args = parser.parse_args()


    print(f"Simulating a global network of {args.nodes} nodes having {args.peers} peers each,")
    if args.mine:
        start = time.process_time()
        N_HASHES = 10000 # number of hashes to compute for benchmarking purposes
        for nonce in range(N_HASHES):
            PoW = Hash(nonce)
        stop = time.process_time()
        print(f"Network hashrate (single core) benchmark: {int(N_HASHES/(stop-start)/1000)} kh/s")
        NETWORK_HASHRATE = N_HASHES/(stop-start)
        node_hashrate = NETWORK_HASHRATE/args.nodes/1000 # kh/s
        bead_time     = MAX_HASH/(2**int(args.target)-1)/NETWORK_HASHRATE
        print(f"mining with difficulty 2**{args.target}-1 and hashrate {int(node_hashrate)}kh/s per node.")
        print(f"We should generate a bead roughly once every {bead_time*1000:{8}.{3}}ms")
        print(f"Expected time to completion: {bead_time*OVERHEAD_FUDGE*int(args.beads):{8}.{3}}s")
    else:
        print("using the geometric distribution to simulate mining.")

    n = Network(int(args.nodes), target=2**int(args.target)-1, npeers=int(args.peers))
    n.simulate(nbeads=int(args.beads), mine=bool(args.mine))
    b = n.nodes[0].braid
    dag = braid.save_braid(dict(b), args.filename, args.description)
    print(f"Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}}")
    print(f"Wrote {len(b.beads)} beads to {args.filename}.")
