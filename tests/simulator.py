#!/usr/bin/env python3
"""
    Braidpool Simulator

    This code simulates a network of nodes distributed on a sphere (the Earth)
    with realistic latency defined by the path length between them on the surface
    of the sphere. Note that all signals are assumed to propagate at the speed
    of light -- propagation speed in copper or global fiber optics is not simulated.
"""

# FIXME give numbers for network and per-node hashrate

# FIXME something is going wrong with the non-mining simulator where it's mostly blockchain-like but
# some beads have very old parents, generating large cohorts.

from argparse import ArgumentParser, BooleanOptionalAction
from copy import copy
from math import pi, sqrt, sin, cos, acos, log, ceil
from random import randint, random, sample
import hashlib
import struct
import sys
import time
import braid
sys.setrecursionlimit(10000) # all_ancestors is recursive. If you generate large cohorts you'll blow
                             # out the maximum recursion depth.

NETWORK_SIZE     = 0.06676  # The round-trip time in seconds to traverse the network = pi*r_e/c
TICKSIZE         = 0.001    # One "tick" in seconds in which beads will be propagated and mined
                            # You can use this as a per-node processing latency also
MAX_HASH         = 2**256-1 # Maximum value a 256 bit unsigned hash can have, to calculate targets
NETWORK_HASHRATE = 800000   # Single core hashrate in hashes/s (will be benchmarked)
OVERHEAD_FUDGE   = 1.95     # Fudge factor for processing overhead compared to pure sha256d mining

def sha256d(msg: bytes):
    """(SHA256^2)(msg) -> bytes"""
    if isinstance(msg, bytes):
        return hashlib.sha256(hashlib.sha256(msg).digest()).digest()
    if isinstance(msg, int):
        return hashlib.sha256(hashlib.sha256(msg.to_bytes(32, byteorder='big')).digest()).digest()
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

class Network:
    """ Abstraction for an entire network containing <n> nodes.  The network has
        a internal clock for simulation which uses <ticksize>.  Latencies are taken
        from a uniform distribution on [0,1) so <ticksize> should be < 1.
    """
    def __init__(self, nnodes, hashrate, ticksize=TICKSIZE, npeers=4, target=None, topology='sphere'):
        self.t                   = 0        # the current "time"
        self.nnodes              = nnodes
        self.hashrate            = hashrate
        self.ticksize            = ticksize # the size of a tick: self.t += self.tick at each step
        self.npeers              = npeers
        self.target              = target
        self.genesis             = uint256(sha256d(0))
        self.beads               = {}
        self.beads[self.genesis] = Bead(self.genesis, set(), self, -1)
        # FIXME asymmetrically divide the hashrate among nodes
        self.nodes               = [Node(self.genesis, self, nodeid, hashrate/nnodes,
                                         initial_target=target) for nodeid in
                                    range(nnodes)]
        latencies                = None
        for (node, peers) in zip(self.nodes, [sample(list(set(range(nnodes)) - {me}),  \
                npeers) for me in range(nnodes)]):
            if topology == 'sphere':
                latencies = [10*sph_arclen(node, self.nodes[i]) for i in peers]
            node.setpeers([self.nodes[i] for i in peers], latencies)
        self.reset(target=target)

    def tick(self, mine=True):
        """ Execute one tick. """

        next_bead_dt = min(self.nodes, key=lambda n:n.tremaining).tremaining
        next_recv_dt = min(self.inflightdelay.values()) if self.inflightdelay else next_bead_dt+NETWORK_SIZE
        dt = self.ticksize if mine else min(next_bead_dt, next_recv_dt)
        self.t += dt
        for (node, bead) in copy(self.inflightdelay):
            self.inflightdelay[(node, bead)] -= dt
            if self.inflightdelay[(node, bead)] <= 0:
                node.receive(bead)
                del self.inflightdelay[(node, bead)]
        for n in self.nodes:
            n.tick(mine=mine, dt=dt)

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
        """ Reset the computed braid for each node while keeping the network layout.  """
        self.t = 0
        self.beads = {}
        self.beads[self.genesis] = Bead(self.genesis, set(), self, -1)
        self.inflightdelay = {}
        for node in self.nodes:
            node.reset(target)

    def printinflightdelays(self):
        """ print in flight delays for debugging. """
        for (node, bead) in self.inflightdelay:
            print("bead ", bead, " to node ", node,
                  " will arrive in %fs"%self.inflightdelay[(node, bead)])

class Node:
    def calc_target_zawy(self, parents):
        """ Calculate a target based on a desired number of parents (2). """
        TARGET_PARENTS = 2
        INTERVAL = 100
        htarget = len(parents)*MAX_HASH//sum([MAX_HASH//p.target for p in parents])
        return htarget + htarget*(TARGET_PARENTS-len(parents))//INTERVAL

    def calc_target_simple(self, parents):
        """ Compute the average target of its parents.  """
        DELTA_NUM   = 2     # FIXME if we change the target too quickly, a string of 1-bead cohorts
        DELTA_DENOM = 32   # will cause the difficulty to hit MAX_HASH and we error out.
        ASYM_FACTOR = 2     # An "asymmetry factor" that reduces the target harder when there are too many parents.
        TARGET_PARENTS = 2
        # Harmonic average parent targets
        htarget = len(parents)*MAX_HASH//sum([MAX_HASH//p.target for p in parents])
        if len(parents) > TARGET_PARENTS:   # Make it more difficult if we have too many parents.
            retval = htarget - ASYM_FACTOR*htarget*DELTA_NUM//DELTA_DENOM*(len(parents) - TARGET_PARENTS)
        elif len(parents) < TARGET_PARENTS: # Make it easier if we have too few parents
            retval = htarget + htarget*DELTA_NUM//DELTA_DENOM
        else:
            retval = htarget
        return retval

    def calc_target_cohort(self, parents):
        """ Compute the average target of its parents.  """
        DELTA_NUM   = 2     # FIXME if we change the target too quickly, a string of 1-bead cohorts
        DELTA_DENOM = 32   # will cause the difficulty to hit MAX_HASH and we error out.
        ASYM_FACTOR = 2     # An "asymmetry factor" that reduces the target harder when there are too many parents.
        TARGET_PARENTS = 2
        # Harmonic average parent targets
        htarget = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)
        if len(parents) > TARGET_PARENTS:   # Make it more difficult if we have too many parents.
            retval = htarget - ASYM_FACTOR*htarget*DELTA_NUM//DELTA_DENOM*(len(parents) - TARGET_PARENTS)
        elif len(parents) < TARGET_PARENTS: # Make it easier if we have too few parents
            retval = htarget + htarget*DELTA_NUM//DELTA_DENOM
        else:
            retval = htarget
        return retval
    """ Abstraction for a node. """
    def __init__(self, genesis, network, nodeid, hashrate, initial_target=None):
        self.genesis    = genesis
        self.network    = network
        self.peers      = []
        self.latencies  = []
        self.nodeid     = nodeid
        # A salt for this node, so all nodes don't produce the same hashes
        self.nodesalt   = uint256(sha256d(randint(0,MAX_HASH)))
        self.hashrate   = hashrate
        self.target     = initial_target
        self.nonce      = 0         # Will be increased in the mining process
        self.tremaining = None      # Ticks remaining before this node produces a bead
        self.calc_target = self.calc_target_simple  # Default target calculation method
        self.reset(initial_target)
        # Geospatial location information
        self.latitude   = pi*(1/2-random())
        self.longitude  = 2*pi*random()

    def reset(self, initial_target=None):
        """ Reset the computed braid while keeping the network layout. """
        self.beads      = [self.network.beads[self.network.genesis]] # A list of beads in the order received
        self.braid      = Braid(self.beads)
        self.incoming   = set()                                      # incoming beads we were unable to process
        self.target     = initial_target
        self.braid.tips = {self.beads[0]}
        self.tremaining = self.time_to_next_bead()

    def __str__(self):
        return f"<Node {self.nodeid}>"

    # Define the geometric distribution instead of importing numpy
    def time_to_next_bead(self):
        """
        Sample from the geometric distribution and compute the expected number of seconds before
        this node with <self.hashrate> finds a block with <self.target>.
        """
        p = self.target/MAX_HASH
        if p > 1:
            raise ValueError(f"target {self.target:064x} is larger than {MAX_HASH:064x}")
        if p < 1e-6: # If p is very small, use a Taylor series to prevent log(1-p) from overflowing
            nhashes = int(log(1 - random()) / -(p+p**2/2+p**3/3+p**4/4+p**5/5)) + 1
        else:
            nhashes = int(log(1 - random()) / log(1 - p)) + 1
        return nhashes/self.hashrate

    def setpeers(self, peers, latencies=None):
        """ Add a peer separated by a latency <delay>. """
        self.peers = peers
        if latencies: self.latencies = latencies
        else:         self.latencies = sample(len(peers))*NETWORK_SIZE
        assert(len(self.peers) == len(self.latencies))

    def tick(self, mine=True, dt=0):
        """ Add a Bead satisfying <target>. """
        oldtips = copy(self.braid.tips)
        b = Bead(None, oldtips, self.network, self.nodeid)
        self.target = b.target
        if mine:
            nhashes = ceil(self.hashrate*dt)
            for _ in range(nhashes):
                PoW = uint256(sha256d(self.nodesalt+self.nonce))
                self.nonce += 1
                if PoW < self.target:
                    print(f" solution target = {b.target:064x} for {len(oldtips)} parents")
                    #print('.', end='', flush=True)
                    b.add_PoW(PoW)
                    self.receive(b)     # Send it to myself (will rebroadcast to peers)
                    break
        else :
            self.tremaining -= dt
            if self.tremaining <= 0:
                print(f" solution target = {b.target:064x} for {len(oldtips)} parents")
                self.nonce += 1
                b.add_PoW((uint256(sha256d(self.nodesalt+self.nonce))*self.target)//MAX_HASH)
                self.receive(b)     # Send it to myself (will rebroadcast to peers)
                self.tremaining = self.time_to_next_bead()
        self.process_incoming()
        if self.braid.tips != oldtips and not mine: # reset mining if we have new tips
            self.tremaining = self.time_to_next_bead()

    def receive(self, bead):
        """ Recieve announcement of a new bead. """
        if bead in self.beads:
            return
        self.beads.append(bead)
        if not self.braid.extend(bead): # We don't have parents for this bead
            self.incoming.add(bead)
        self.process_incoming()
        self.send(bead)

    def process_incoming(self):
        """ Process any beads in self.incoming that have not yet been added because of missing
            parents.
        """
        while True:
            oldincoming = copy(self.incoming)
            for bead in oldincoming:
                if self.braid.extend(bead):
                    self.incoming.remove(bead)
            if oldincoming == self.incoming:
                break

    def send(self, bead):
        """ Announce a new block from a peer to this node. """
        for (peer, delay) in zip(self.peers, self.latencies):
            self.network.broadcast(peer, bead, delay)

class Bead:
    """ A Bead is a full bitcoin (weak) block that may miss Bitcoin's difficulty target.
    """

    def __init__(self, hash, parents, network, creator):
        """ All attributes of this object should be serializable on the network
            and not refer to internal data structures. """
        self.t = network.t
        self.hash = hash    # a hash that identifies this block
        self.parents = parents
        self.network = network
        self.creator = creator
        if creator != -1: # if we're not the genesis block (which has no creator node)
            self.target = network.nodes[creator].calc_target(self.parents)
        else:
            self.target = network.target
        if hash is not None:
            network.beads[hash] = self # add myself to global list

    def __str__(self):
        return f"<Bead ...{self.hash%10000}>"

    def add_PoW(self, hash):
        """ Add proof of work hash after it is computed. """
        self.hash = hash
        self.network.beads[hash] = self


class Braid:
    """ A Braid is a Directed Acyclic Graph with no incest (parents may not also
        be non-parent ancestors).  A braid may have multiple tips. """

    def __init__(self, beads=None, filename=None):
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
            print("FIXME loading from a file unimplemented.")

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
        if (not bead.parents                                             # No parents: bad block
                or not all(p.hash in self.vhashes for p in bead.parents) # Don't have all parents
                or bead in self.beads):                                  # Already seen this bead
            return False
        self.beads.append(bead)
        self.vhashes[bead.hash]   = bead
        for p in bead.parents:
            self.times[bead.hash] = bead.t
            if p in self.tips:
                self.tips.remove(p)
        self.tips.add(bead)
        return True

def main():
    """ Main function so it doesn't make a bunch of globals. """
    global NETWORK_HASHRATE
    parser = ArgumentParser()
    parser.add_argument("-o", "--output-file", dest="filename",
        help="Base filename to which we will write the generated braid, '.json' will be added",
        default="braid")
    parser.add_argument("-n", "--nodes",
        help="Number of nodes to simulate",
        default=25)
    parser.add_argument("--mine", action=BooleanOptionalAction,
        help="Do sha256d mining (if --no-mine we will use a geometric distribution)",
        default = False)
    parser.add_argument("-t", "--target",
        help="Target difficulty exponent t where T=2**t-1",
        default=239)
    parser.add_argument("-b", "--beads",
        help="Number of beads to simulate",
        default=50)
    parser.add_argument("-p", "--peers",
        help="Number of peers per node",
        default=4)
    parser.add_argument("-d", "--description",
        help="String description describing this simulation run",
        default="No description provided")
    parser.add_argument("-T", "--test", action=BooleanOptionalAction,
        help="Test mining vs no-mining mode",
        default=False)
    args = parser.parse_args()

    print(f"Simulating a global network of {args.nodes} nodes having {args.peers} peers each,")
    if args.mine:
        start = time.process_time()
        N_HASHES = 10000 # number of hashes to compute for benchmarking purposes
        for nonce in range(N_HASHES):
            sha256d(nonce)
        stop = time.process_time()
        print(f"Network hashrate (single core) benchmark: {int(N_HASHES/(stop-start)/1000)} kh/s")
        NETWORK_HASHRATE = N_HASHES/(stop-start)
        bead_time     = MAX_HASH/(2**int(args.target)-1)/NETWORK_HASHRATE
        print(f"mining with difficulty 2**{args.target}-1 and hashrate "
              "{int(node_hashrate/1000)}kh/s per node.")
        print(f"We should generate a bead roughly once every {bead_time*1000:{8}.{4}}ms")
        print(f"Expected time to completion: {bead_time*OVERHEAD_FUDGE*int(args.beads):{8}.{4}}s "
              "to mine {args.beads} beads")
        print("Printing a dot every time a bead is mined: ")
    else:
        print("using the geometric distribution to simulate mining.")

    target = 2**int(args.target)-1
    n = Network(int(args.nodes), NETWORK_HASHRATE, target=target, npeers=int(args.peers))
    if args.test:
        n.simulate(nbeads=int(args.beads), mine=True)
        bmine   = copy(n.nodes[0].braid)
        dag = braid.save_braid(dict(bmine), args.filename+"-mine.json", args.description)
        Nc = len(dag['cohorts'])
        Ncerr = 1/sqrt(Nc)
        print(f"\n   mined Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}} +/- {Ncerr:{5}.{4}}")
        print(f"Wrote {len(bmine.beads)} beads to {args.filename}-mine.json.")
        n.reset(target)
        n.simulate(nbeads=int(args.beads), mine=False)
        bnomine = copy(n.nodes[0].braid)
        dag = braid.save_braid(dict(bnomine), args.filename+"-no-mine.json", args.description)
        Nc = len(dag['cohorts'])
        Ncerr = 1/sqrt(Nc)
        print(f"\nno-mined Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}} +/- {Ncerr:{5}.{4}}")
        print(f"Wrote {len(bnomine.beads)} beads to {args.filename}-no-mine.json.")
    else:
        n.simulate(nbeads=int(args.beads), mine=bool(args.mine))
        b = copy(n.nodes[0].braid)
        dag = braid.save_braid(dict(b), args.filename+".json", args.description)
        Nc = len(dag['cohorts'])
        Ncerr = 1/sqrt(Nc)
        print(f"\nno-mined Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}} +/- {Ncerr:{5}.{4}}")
        print(f"Wrote {len(b.beads)} beads to {args.filename}.json.")

if __name__ == "__main__":
    main()
