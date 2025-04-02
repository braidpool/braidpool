#!/usr/bin/env python3
"""
    Braidpool Simulator

    This code simulates a network of nodes distributed on a sphere (the Earth)
    with realistic latency defined by the path length between them on the surface
    of the sphere. Note that all signals are assumed to propagate at the speed
    of light -- propagation speed in copper or global fiber optics is not simulated.
"""

from argparse import ArgumentParser, BooleanOptionalAction
from collections import OrderedDict
from copy import copy
import math
from math import pi, sqrt, sin, cos, acos, log, ceil, exp
import numpy as np
from scipy.optimize import curve_fit
from fractions import Fraction
from typing import Iterable
import random
import hashlib
import re
import struct
import sys
import time
from scipy.special import lambertw as W
from numpy import real
import braid
import matplotlib.pyplot as plt
sys.setrecursionlimit(10000) # all_ancestors is recursive. If you generate large cohorts you'll blow
                             # out the maximum recursion depth.

NETWORK_SIZE     = 0.06676   # The round-trip time in seconds to traverse the network = pi*r_e/c
TICKSIZE         = 0.001     # One "tick" in seconds in which beads will be propagated and mined
                             # You can use this as a per-node processing latency also
MAX_HASH         = 2**256-1  # Maximum value a 256 bit unsigned hash can have, to calculate targets
NETWORK_HASHRATE = 800000    # Single core hashrate in hashes/s (will be benchmarked)
OVERHEAD_FUDGE   = 1.95      # Fudge factor for processing overhead compared to pure sha256d mining
EARTH_RADIUS     = 6371000   # Mean radius of earth in meters
SPEED_OF_LIGHT   = 299792458 # speed of light in m/s
MAX_CACHE        = 100       # Maximum number of cohorts to cache
DEBUG            = False

# Good integer choices that closely approximate (W(1/2)+1)/W(1/2) = 2.421529936
# If N_C is too large here, the last cohort can become very large and N_B/N_C grows slowly because
# the window is large, so the difficulty doesn't adjust downward quickly enough.
# 17/7=2.42857    (error= 0.00704149)   fft peak is barely visible          4*17*NETWORK_SIZE:  4.54s
# 46/19=2.42105   (error=-0.000477304)  fft peak @ 0.0420 Hz = 23.8s (broad around this)
# 75/31=2.41935   (error=-0.0021751)    fft peak @ 0.0328 Hz = 30.5s (20*NETWORK_SIZE) Period: 25.2s
# 138/57=2.42105  (error=-0.000477304)  fft peak @ 0.0246 Hz = 40.7s (22*NETWORK_SIZE) Period: 35.8s
# 201/83=2.42169  (error= 0.000156811)  fft peak @ 0.01877Hz = 53.3s (39*NETWORK_SIZE) Period: 51.9s (secondary peak @ 26.2s)
# 247/102=2.42157 (error= 0.0000386915) fft peak @ 0.01582Hz = 63.2s (50*NETWORK_SIZE) Period: 60.4s (secondary peak @ 30.9s)
# 540/223=2.42152 (error=-0.0000052732) fft peak @ 0.00781Hz = 128s (205*NETWORK_SIZE) Period: 122s  (secondary peak @ 62.6s)
# others:
# 121/50=2.42       (error=-0.00152994)
# 63/26=2.42308     (error= 0.00154699)
# Period seems to be 4*NB*NETWORK_SIZE
TARGET_NC = 7
TARGET_NB = 17
TARGET_DAMPING = 4*TARGET_NB

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

def print_hash_simple(h:int):
    return f"{h>>(256-32):08x}"

def print_hash(h):
    """
    Prints a string to the console with the color specified by the hash for easy visual
    identification.
    """
    if type(h) == int or hasattr(h, 'hash'):
        hex_string = f"{h:064x}" if type(h) == int else f"{h.hash:064x}"
        color = re.search(r'0*.([^0].{5})', hex_string).group(1)
        # Convert hex to RGB
        r, g, b = tuple(int(color[i:i+2], 16) for i in (0, 2, 4))
        # ANSI escape code for setting color
        color_code = f"\033[38;2;{r};{g};{b}m"
        reset_code = "\033[0m"  # Reset to default color
        # Print with color
        return f"{color_code}{hex_string[:8]}{reset_code}"
    elif isinstance(h, dict):
        retval = "{"
        for k,v in h.items():
            retval += f"{print_hash(k)}: {print_hash(v)}"
            if (k,v) != list(h.items())[-1]:
                retval += ", "
        retval += "}"
        return retval
    elif isinstance(h, Iterable):
        retval = "["
        if isinstance(h, set):
            retval = "{"
        nprinted = 0
        for i in h:
            nprinted += 1
            retval += print_hash(i)
            if nprinted != len(h):
                retval += ", "
        if isinstance(h, set):
            retval += "}"
        else:
            retval += "]"
        return retval
    else:
        raise Exception("Unknown type passed to print_hash: ", type(h))

class Network:
    """ Abstraction for an entire network containing <n> nodes.  The network has
        a internal clock for simulation which uses <ticksize>.  Latencies are taken
        from a uniform distribution on [0,1) so <ticksize> should be < 1.
    """
    def __init__(self, nnodes, hashrate=NETWORK_HASHRATE, ticksize=TICKSIZE, npeers=4, target=None,
                 target_algo=None, log=False):
        self.t                   = 0.0      # the current "time"
        self.nnodes              = nnodes
        self.hashrate            = hashrate
        self.ticksize            = ticksize # the size of a tick: self.t += self.tick at each step
        self.npeers              = npeers
        self.target              = target if target is not None else MAX_HASH // 1000
        self.log                 = log
        self.genesis_hash        = uint256(sha256d(0))
        self.genesis_bead        = Bead(self.genesis_hash, set(), self, -1)
        # FIXME asymmetrically divide the hashrate among nodes
        self.cohort_cache        = OrderedDict() # Keep a global cohort cache so nodes
                                                 # don't have to repeat cohorts calculations.
                                                 # This is also passed as the ancestor cache to cohorts()
                                                 # (they use different keys for cohorts and ancestors)
        self.nodes               = [Node(self.genesis_bead, self, nodeid, hashrate/nnodes/NETWORK_SIZE,
                                         initial_target=target, log=log,
                                         cohort_cache=self.cohort_cache) for nodeid in
                                    range(nnodes)]
        # FIXME initial target should be calcluated to produce a bead once every <NETWORK_SIZE>?
        latencies                = None
        out_peers = {}
        for (nodeid, peers) in zip(range(nnodes), [random.sample(list(set(range(nnodes)) - {me}),  \
                npeers) for me in range(nnodes)]):
            latencies = [NETWORK_SIZE*sph_arclen(self.nodes[nodeid], self.nodes[p]) for p in peers]
            self.nodes[nodeid].add_peers([self.nodes[p] for p in peers], latencies)
            out_peers[nodeid] = peers
        for nodeid in range(nnodes):
            self.nodes[nodeid].reset(target, target_algo)
        # Compute incoming peers
        in_peers = {nodeid: [] for nodeid in range(nnodes)}
        for nodeid,peers in out_peers.items():
            for peer in peers:
                in_peers[peer].append(nodeid)
        for nodeid,peers in in_peers.items():
            latencies = [NETWORK_SIZE*sph_arclen(self.nodes[nodeid], self.nodes[p]) for p in peers]
            self.nodes[nodeid].add_peers([self.nodes[p] for p in in_peers[nodeid]], latencies)

        self.reset(target, target_algo)
        # FIXME we need to make sure no peers are isolated, we could have a disjoint network.

        if DEBUG:
            print(f"# Starting network with genesis bead {print_hash(self.genesis_hash)} at time {self.t:12.8}")

    def tick(self, mine=True):
        """ Execute one tick. """

        next_bead_dt = min(self.nodes, key=lambda n:n.tremaining).tremaining
        next_recv_dt = min(self.inflightdelay.values()) if self.inflightdelay else next_bead_dt+NETWORK_SIZE
        dt = self.ticksize if mine else min(next_bead_dt, next_recv_dt)
        self.t += dt
        for (nodeid, bead) in copy(self.inflightdelay):
            self.inflightdelay[(nodeid, bead)] -= dt
            if self.inflightdelay[(nodeid, bead)] <= 0:
                self.nodes[nodeid].receive(bead)
                del self.inflightdelay[(nodeid, bead)]
        for n in self.nodes:
            n.tick(mine=mine, dt=dt)

    def simulate(self, nbeads=20, mine=False):
        """ Simulate the network until we have added <nbeads> beads """
        initial_beads = len(self.nodes[0].braid.beads)
        while len(self.nodes[0].braid.beads) < initial_beads + nbeads:
            self.tick(mine=mine)

    def broadcast(self, node, bead, delay):
        """ Announce a block/bead discovery to a node who is <delay> away. """
        if bead not in node.braid:
            prevdelay = NETWORK_SIZE
            if (node.nodeid,bead) in self.inflightdelay:
                prevdelay = self.inflightdelay[(node.nodeid, bead)]
            self.inflightdelay[(node.nodeid, bead)] = min(prevdelay, delay)

    def reset(self, target=None, target_algo=None):
        """ Reset the computed braid for each node while keeping the network layout.  """
        self.t                   = 0.0
        self.inflightdelay       = {}
        for node in self.nodes:
            node.reset(target, target_algo)

    def print_in_flight_delays(self):
        """ print in flight delays for debugging. """
        for (node, bead) in self.inflightdelay:
            print(f"bead {bead} to node {node} will arrive in {self.inflightdelay[(node, bead)]}s")
        else:
            print("There are no beads in flight.")

class Node:
    """ Abstraction for a node. """
    def __init__(self, genesis_bead, network, nodeid, hashrate,
                 initial_target=None, cohort_cache=None, log=False):
        self.genesis_bead = genesis_bead
        self.network      = network
        self.peers        = []
        self.latencies    = []
        self.nodeid       = nodeid
        self.cohort_cache = cohort_cache # Store the cohort cache on the network
                                         # object and pass it by reference to Braid.extend()
        # PID controller state
        self.prev_errors = []  # Store previous errors for integral and derivative terms
        self.max_error_history = 10  # Maximum number of errors to store
        # A salt for this node, so all nodes don't produce the same hashes
        self.nodesalt     = uint256(sha256d(random.randint(0,MAX_HASH)))
        self.hashrate     = hashrate
        self.target       = initial_target if initial_target is not None else network.target
        self.log          = log
        self.nonce        = 0         # Will be increased in the mining process
        self.tremaining   = None      # Ticks remaining before this node produces a bead
        self.incoming     = set()     # Initialize incoming set
        self.calc_target  = self.calc_target_simple # Default target calculation method
        # A braid of all beads for this node
        self.braid        = Braid([genesis_bead])
        self.braid.tips   = {list(self.braid.beads.values())[0]}
        self.working_bead = Bead(None, frozenset(self.braid.tips), self.network, self.nodeid)
        # Geospatial location information
        self.latitude     = pi*(1/2-random.random())
        self.longitude    = 2*pi*random.random()

    def reset(self, initial_target=None, target_algo=None):
        """ Reset the computed braid while keeping the network layout. This must be called after the
            geospatial information for all nodes is filled in, to calculate self.tremaining if not
            mining.
        """
        self.braid        = Braid([self.genesis_bead])
        self.braid.tips   = {list(self.braid.beads.values())[0]}
        self.incoming     = set()                                        # incoming beads we were unable to process
        if initial_target is not None:
            self.target   = initial_target
        elif self.network.target is not None:
            self.target   = self.network.target

        if self.target is not None:
            self.tremaining   = self.time_to_next_bead()
        self.working_bead = Bead(None, frozenset(self.braid.tips), self.network, self.nodeid)

        # Reset controller state
        self.prev_errors = []
        self.target_history = []  # For model-based controller

        if target_algo is None or target_algo == "fixed":
            self.calc_target = self.calc_target_fixed
        elif target_algo == "exp":
            self.calc_target = self.calc_target_exponential_damping
        elif target_algo == "parents":
            self.calc_target = self.calc_target_parents
        elif target_algo == "simple":
            self.calc_target = self.calc_target_simple
        elif target_algo == "instant":
            self.calc_target = self.calc_target_instant
        elif target_algo == "pid":
            self.calc_target = self.calc_target_pid
        elif target_algo == "model":
            self.calc_target = self.calc_target_model
        elif target_algo == "simple_asym":
            self.calc_target = self.calc_target_simple_asym
        elif target_algo == "simple_asym_damped":
            self.calc_target = self.calc_target_simple_asym_damped

    def __str__(self):
        return f"<Node {self.nodeid}>"

    # Define the geometric distribution instead of importing numpy
    def time_to_next_bead(self):
        """
        Sample from the geometric distribution and compute the expected number of seconds before
        this node with <self.hashrate> finds a block with <self.target>.
        """
        p = self.target/MAX_HASH
        if p >= 1.0:
            raise ValueError(f"target {self.target:064x} is larger than {MAX_HASH:064x}")
        try:
            r = random.random()
            if p < 1e-6: # If p is very small, use a Taylor series to prevent log(1-p) from overflowing
                nhashes = int(log(1 - r) / -(p+p**2/2+p**3/3+p**4/4+p**5/5)) + 1
            else:
                nhashes = int(log(1 - r) / log(1 - p)) + 1
        except ValueError as e:
            print(f"{e}: p={p} r={r}")
            raise
        return nhashes/self.hashrate

    def add_peers(self, peers, latencies):
        """ Add a peer separated by a latency <delay>. """
        self.peers.extend(peers)
        self.latencies.extend(latencies)

    def tick(self, mine=True, dt=0):
        """ Add a Bead satisfying <target>. """

        if not mine:
            self.tremaining -= dt
            if not self.incoming and self.braid.tips == self.working_bead.parents and self.tremaining > 0:
                return
        oldtips = copy(self.braid.tips)
        added_bead = None
        if oldtips != self.working_bead.parents:
            self.working_bead = Bead(None, oldtips, self.network, self.nodeid)
        if mine:
            nhashes = ceil(self.hashrate*dt)
            for _ in range(nhashes):
                PoW = uint256(sha256d(self.nodesalt+self.nonce))
                self.nonce += 1
                if PoW < self.target:
                    Nb = sum(map(len, self.braid.cohorts[-TARGET_NC:]))
                    self.working_bead.add_PoW(PoW)
                    added_bead = copy(self.working_bead)
                    self.receive(self.working_bead)     # Send it to myself (will rebroadcast to peers)
                    break
        else :
            if self.tremaining <= 0:
                Nb = sum(map(len, self.braid.cohorts[-TARGET_NC:]))
                self.nonce += 1
                self.working_bead.add_PoW((uint256(sha256d(self.nodesalt+self.nonce))*self.target)//MAX_HASH)
                added_bead = copy(self.working_bead)
                self.tremaining = self.time_to_next_bead()
                self.receive(self.working_bead)
        if self.log and added_bead:
            print(f"== Solution {print_hash(added_bead.hash)} "
                  f"target = {added_bead.target>>(256-32):08x}... for cohort size "
                  f"{len(self.braid.cohorts[-2]):3} on node {self.nodeid:2} "
                  f"at time {self.network.t:12.6f} Nb/Nc={Nb/TARGET_NC:12.6}") # moving average
            if DEBUG:
                print(f"    Having parents: {print_hash([p.hash for p in self.working_bead.parents])}")
        self.process_incoming()
        if self.braid.tips != oldtips and not mine: # reset mining if we have new tips
            self.tremaining = self.time_to_next_bead()

    def receive(self, bead):
        """ Recieve announcement of a new bead. """
        if bead in self.braid:
            return
        self.incoming.add(bead)
        self.process_incoming()
        self.working_bead = Bead(None, copy(self.braid.tips), self.network, self.nodeid)
        self.target = self.working_bead.target = self.calc_target(self.working_bead.parents)
        self.tremaining = self.time_to_next_bead()
        self.send(bead)
        if DEBUG:
            print(f"Node {self.nodeid:2} received bead {print_hash(bead.hash)} at time {self.network.t:12.6f} "
                  f"we have {len(self.braid.tips)} tips: {print_hash([t.hash for t in self.braid.tips])}")

    def process_incoming(self):
        """ Process any beads in self.incoming that have not yet been added because of missing
            parents.
        """
        while True:
            oldincoming = copy(self.incoming)
            for bead in oldincoming:
                if self.braid.extend(bead, cohort_cache=self.cohort_cache,
                                     compute_cohorts=False if self.calc_target == self.calc_target_fixed
                                     else True):
                    self.incoming.remove(bead)
                elif DEBUG:
                    print(f"Node {self.nodeid} unable to add {print_hash(bead.hash)} to braid, missing parents")
            if oldincoming == self.incoming:
                break

    def send(self, bead):
        """ Announce a new block from this node to all peers. """
        for (peer, delay) in zip(self.peers, self.latencies):
            self.network.broadcast(peer, bead, delay)

    def calc_target_fixed(self, parents):
        """ Use a fixed target (constant difficulty) """
        return self.target

    def calc_target_parents(self, parents):
        """ Calculate a target based on a desired number of parents, targeting 2.
            h/t @zawy

            This method could form a huge cohort and we wouldn't know it.
        """
        TARGET_PARENTS = 2
        INTERVAL = 100
        htarget = len(parents)*MAX_HASH//sum([MAX_HASH//p.target for p in parents])
        return htarget + htarget*(TARGET_PARENTS-len(parents))//INTERVAL

    def calc_target_simple(self, parents):
        """ Calculate a target based on the number of cohorts using TARGET_NB and TARGET_NC where
            TARGET_NB/TARGET_NC =~ 2.42, and we use a constant correction factor to adjust the
            difficulty up if there are too many cohorts, and down if there are too few cohorts.
            This results in oscillation with a period 2*TARGET_NB.
        """
        DELTA_NUM   = 2     # FIXME if we change the target too quickly, a string of 1-bead cohorts
        DELTA_DENOM = 128   # will cause the difficulty to hit MAX_HASH and we error out.
                            # A cohort larger than DELTA_NUM/DELTA_DENOM will cause the new target to be negative.

        Nb = sum(map(len,self.braid.cohorts[-TARGET_NC:]))
        Nb_Nc = Nb/len(self.braid.cohorts[-TARGET_NC:])

        # Harmonic average parent targets
        htarget = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)
        if Nb > TARGET_NB:   # Make it more difficult if cohort is too large
            retval = htarget - htarget*DELTA_NUM//DELTA_DENOM
        elif Nb < TARGET_NB: # Make it easier if cohort is too small
            retval = htarget + htarget*DELTA_NUM//DELTA_DENOM
        else:
            retval = htarget
        return retval

    def calc_target_instant(self, parents):
        """ Calculate a target based on the number of cohorts using TARGET_NB and TARGET_NC where
            TARGET_NB/TARGET_NC =~ 2.42. Herein we compute the desired value of x_0 given the
            harmonic average of our parents x_1 as:
                x_0 = 2 x_1 W(1/2)/W(N_B/N_C-1)
            FIXME this fails if N_B/N_C = 1
            FIXME we can enumerate values for W(N_B/N_C-1): see "LambertW Fractions.ipynb"
        """
        Nb = sum(map(len,self.braid.cohorts[-TARGET_NC:]))
        Nb_Nc = Nb/len(self.braid.cohorts[-TARGET_NC:])

        # Harmonic average parent targets
        x_1 = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)
        return 2*x_1*W(1/2)/W(Nb_Nc-1)

    # Model function for Nb/Nc ratio
    def model_nb_nc_ratio(self, x, a, lambda_val):
        """
        Model the relationship between target difficulty (x) and Nb/Nc ratio
        using the formula: Nb/Nc = 1 + a*λ*x*exp(a*λ*x)

        Args:
            x: Target difficulty
            a: Constant related to network propagation
            lambda_val: Constant related to mining rate

        Returns:
            Predicted Nb/Nc ratio
        """
        print(f"model_nb_nc_ratio: x={x} a={a} lambda={lambda_val}")
        return 1 + a * lambda_val * x * exp(a * lambda_val * x)

    # Inverse function to solve for x given a desired Nb/Nc ratio
    def solve_for_target(self, desired_ratio, a, lambda_val, x_initial=None):
        """
        Solve for the target difficulty (x) that would give the desired Nb/Nc ratio

        Args:
            desired_ratio: Target Nb/Nc ratio
            a: Estimated parameter a
            lambda_val: Estimated parameter λ
            x_initial: Initial guess for x

        Returns:
            Estimated target difficulty
        """
        if desired_ratio <= 1:
            return MAX_HASH  # Maximum difficulty for ratios <= 1

        # Use current target as initial guess if not provided
        if x_initial is None:
            x_initial = self.target

        # Simple iterative solver using Newton's method
        x = x_initial/MAX_HASH
        max_iter = 10
        tolerance = 1e-6

        for _ in range(max_iter):
            # Current function value
            f_x = self.model_nb_nc_ratio(x, a, lambda_val) - desired_ratio

            # If we're close enough, return the result
            if abs(f_x) < tolerance:
                break

            # Derivative of the function with respect to x
            df_dx = a * lambda_val * exp(a * lambda_val * x) * (1 + a * lambda_val * x)

            # Newton's method update
            x_new = x - f_x / df_dx

            # Ensure x stays positive
            x = max(1, x_new)*MAX_HASH

        return int(x)

    def estimate_model_parameters(self):
        """
        Estimate the parameters a and λ from historical data

        Returns:
            Tuple of (a, λ)
        """
        # Need at least a few data points to estimate parameters
        if not hasattr(self, 'target_history') or len(self.target_history) < 5:
            # Return default values if we don't have enough data
            return 0.1, 0.01

        # Extract x values (targets) and y values (Nb/Nc ratios)
        x_data = np.array([t for t, _ in self.target_history])
        y_data = np.array([r for _, r in self.target_history])

        # Normalize x data to avoid numerical issues
        x_scale = np.mean(x_data)
        x_data_norm = x_data / x_scale

        # Initial parameter guess
        p0 = [0.1, 0.01]

        try:
            # Define the model function for curve fitting
            def fit_func(x, a, lambda_val):
                return 1 + a * lambda_val * x * np.exp(a * lambda_val * x)

            # Fit the model to the data
            popt, _ = curve_fit(fit_func, x_data_norm, y_data, p0=p0, bounds=([0, 0], [10, 10]))

            # Adjust lambda for the scaling we applied
            a_est, lambda_est = popt
            lambda_est = lambda_est / x_scale

            return a_est, lambda_est

        except (RuntimeError, ValueError):
            # If curve fitting fails, return default values
            return 0.1, 0.01

    def calc_target_model(self, parents):
        """ Calculate a target based on the analytic model of the relationship between
            target difficulty and Nb/Nc ratio: N_B/N_C = 1 + a*λ*x*exp(a*λ*x)

            This approach directly solves for the target difficulty that would give
            the desired Nb/Nc ratio, based on estimated parameters a and λ.
        """
        # Get the current state
        Nb = sum(map(len, self.braid.cohorts[-TARGET_NC:]))
        Nc = len(self.braid.cohorts[-TARGET_NC:])
        Nb_Nc = Nb/Nc

        # Target ratio we want to achieve
        target_ratio = TARGET_NB/TARGET_NC

        # Harmonic average of parent targets
        x_1 = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)

        # Initialize target history if it doesn't exist
        if not hasattr(self, 'target_history'):
            self.target_history = []

        # Add current data point to history
        self.target_history.append((x_1, Nb_Nc))

        # Keep history at a reasonable size
        max_history = 20
        if len(self.target_history) > max_history:
            self.target_history = self.target_history[-max_history:]

        # Estimate model parameters
        a, lambda_val = self.estimate_model_parameters()

        # Solve for the target that would give the desired ratio
        new_target = self.solve_for_target(target_ratio, a, lambda_val, x_1)

        # Apply a damping factor to avoid large jumps
        damping = 0.7
        new_target = int(damping * new_target + (1 - damping) * x_1)

        # Ensure target stays within reasonable bounds
        new_target = max(1, min(MAX_HASH, new_target))

        if self.log and self.nodeid == 0:
            print(f"MODEL: Nb/Nc={Nb_Nc:.4f} Target={target_ratio:.4f} "
                  f"a={a:.6f} λ={lambda_val:.6f} "
                  f"Old={print_hash_simple(x_1)} New={print_hash_simple(new_target)}")

        return new_target

    def calc_target_pid(self, parents):
        """ Calculate a target based on the number of cohorts using TARGET_NB and TARGET_NC where
            TARGET_NB/TARGET_NC =~ 2.42. Herein we use a Proportional Integral Derivative (PID)
            controller to adjust the difficulty up if there are too many cohorts, and down if
            there are too few cohorts.

            The analytic behavior follows: N_B/N_C = 1 + a*λ*x*exp(a*λ*x)
            where:
            - a is a constant related to network propagation
            - λ is related to the mining rate
            - x is our control variable (target difficulty)
        """
        # Get the current state
        Nb = sum(map(len, self.braid.cohorts[-TARGET_NC:]))
        Nc = len(self.braid.cohorts[-TARGET_NC:])
        Nb_Nc = Nb/Nc

        # Calculate the error (difference between current and target ratio)
        target_ratio = TARGET_NB/TARGET_NC
        error = target_ratio - Nb_Nc

        # PID controller parameters - these values can be optimized with --pid-calibrate
        Kp = 0.05  # Proportional gain
        Ki = 0.00  # Integral gain
        Kd = 0.02  # Derivative gain

        # Harmonic average of parent targets
        x_1 = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)

        # Proportional term
        p_term = Kp * error

        # Integral term - sum of all previous errors
        self.prev_errors.append(error)
        if len(self.prev_errors) > self.max_error_history:
            self.prev_errors.pop(0)  # Remove oldest error
        i_term = Ki * sum(self.prev_errors)

        # Derivative term - rate of change of error
        d_term = 0
        if len(self.prev_errors) >= 2:
            d_term = Kd * (self.prev_errors[-1] - self.prev_errors[-2])

        # Combine terms to get the adjustment factor
        adjustment = p_term + i_term + d_term

        # Apply adjustment to the target using a constrained approach
        # Use tanh-like function to limit adjustment to [-0.9, 0.9] range
        # This ensures we never adjust by more than 90% in either direction
        constrained_adjustment = 0.9 * (2 / (1 + math.exp(-2 * adjustment)) - 1)

        # Positive error means Nb/Nc is too low, so increase target (make mining easier)
        # Negative error means Nb/Nc is too high, so decrease target (make mining harder)
        new_target = int(x_1 * (1 + constrained_adjustment))

        # Additional safety check to ensure target stays within reasonable bounds
        new_target = max(1, min(MAX_HASH, new_target))

        if self.log and self.nodeid == 0:
            print(f"PID: Nb/Nc={Nb_Nc:.4f} Target={target_ratio:.4f} Error={error:.4f} "
                  f"P={p_term:.4f} I={i_term:.4f} D={d_term:.4f} "
                  f"Adjustment={adjustment:.4f} Old={print_hash_simple(x_1)} New={print_hash_simple(new_target)}")

        return new_target

    def calc_target_exponential_damping(self, parents):
        """ Calculate a target based on the number of cohorts using TARGET_NB and TARGET_NC where
            TARGET_NB/TARGET_NC =~ 2.42, and we use an exponential correction factor to adjust the
            difficulty up if there are too many cohorts, and down if there are too few cohorts.
            This is intended to damp oscillations.
        """
        Nb = sum(map(len,self.braid.cohorts[-TARGET_NC:]))
        Adev = Nb-TARGET_NB
        TAU = TARGET_DAMPING # 64 is underdamped

        # Harmonic average parent targets
        # x = htarget*exp(-(N_B-TARGET_NB)/TAU)
        htarget = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)
        retval = + htarget \
                 - htarget*Adev//TAU \
                 + htarget*Adev**2//TAU**2//2 \
                 - htarget*Adev**3//TAU**3//6 \
                 + htarget*Adev**4//TAU**4//24 \
                 - htarget*Adev**5//TAU**5//120
        return retval


    def calc_target_simple_asym(self, parents):
        """ Calculate a target based on the number of cohorts using TARGET_NB and TARGET_NC where
            TARGET_NB/TARGET_NC =~ 2.42, and we use a constant correction factor to adjust the
            difficulty up if there are too many cohorts, and down if there are too few cohorts.
            This results in oscillation with a period 2*TARGET_NB.

            FIXME WIP: This version uses an asymmetry factor taken from the Lambert W function.
        """
        DELTA_NUM   = 2     # FIXME if we change the target too quickly, a string of 1-bead cohorts
        DELTA_DENOM = TARGET_NC # will cause the difficulty to hit MAX_HASH and we error out.
                            # A cohort larger than DELTA_NUM/DELTA_DENOM will cause the new target to be negative.
        W12 = Fraction(0.35173371124919584) # Lambert $W(1/2)$

        Nc = TARGET_NC
        Nb = sum(map(len,self.braid.cohorts[-TARGET_NC:]))
        # Harmonic average parent targets
        htarget = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)

        loops = 0
        while Nb <= Nc: # Keep expanding the Nc until we have Nb != Nc
            loops += 1
            Nc *= 2
            if Nc >= len(self.braid.beads): # We started with difficulty too high
                return htarget+htarget//32 # and have no Nc measure for a
            Nb = sum(map(len,self.braid.cohorts[-Nc:]))
        if loops > 0:
            print(f"loops = {loops}")
        Nb_Nc = Nb/Nc

        # Compute the asymmetry factor
        WRm1 = Fraction(W(Nb_Nc-1).real)
        x0 = 2*htarget*W12.numerator*WRm1.denominator//W12.denominator//WRm1.numerator
        dx = x0-htarget

        htarget += dx*DELTA_NUM//DELTA_DENOM
        return htarget

    def calc_target_simple_asym_damped(self, parents):
        """ Calculate a target based on the number of cohorts using TARGET_NB and TARGET_NC where
            TARGET_NB/TARGET_NC =~ 2.42, and we use a constant correction factor taken from the
            Lambert W function to adjust the difficulty up if there are too many cohorts, and down
            if there are too few cohorts. We then apply exponential damping.

            FIXME WIP: This doesn't work.
        """
        DELTA_NUM   = 2     # FIXME if we change the target too quickly, a string of 1-bead cohorts
        DELTA_DENOM = TARGET_NC # will cause the difficulty to hit MAX_HASH and we error out.
                            # A cohort larger than DELTA_NUM/DELTA_DENOM will cause the new target to be negative.
        W12 = Fraction(0.35173371124919584) # Lambert $W(1/2)$

        Nc = TARGET_NC
        Nb = sum(map(len,self.braid.cohorts[-TARGET_NC:]))
        # Harmonic average parent targets
        htarget = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)

        loops = 0
        while Nb <= Nc: # Keep expanding the Nc until we have Nb != Nc
            loops += 1
            Nc *= 2
            if Nc >= len(self.braid.beads): # We started with difficulty too high
                return htarget+htarget//32 # and have no Nc measure for a
            Nb = sum(map(len,self.braid.cohorts[-Nc:]))
        if loops > 0:
            print(f"loops = {loops}")
        Nb_Nc = Nb/Nc

        # Compute the asymmetry factor
        WRm1 = Fraction(W(Nb_Nc-1).real)
        x0 = 2*htarget*W12.numerator*WRm1.denominator//W12.denominator//WRm1.numerator
        dx = x0-htarget

        # Exponential damping
        Adev = Nb-TARGET_NB
        TAU = TARGET_DAMPING

        #htarget += dx*DELTA_NUM//DELTA_DENOM
        #htarget += dx

        # x = htarget*exp(-(N_B-TARGET_NB)/TAU)
        #retval = + (htarget+dx) \
        #         - (htarget+dx)*(dx   //htarget   //TAU) \
        #         + (htarget+dx)*(dx**2//htarget**2//TAU**2//2) \
        #         + (htarget+dx)*(dx**3//htarget**3//TAU**3//6) \
        #         - (htarget+dx)*(dx**4//htarget**4//TAU**4//24) \
        #         + (htarget+dx)*(dx**5//htarget**5//TAU**5//120)
        # x = htarget + dx*(exp(-(dx/htarget/TAU)))
        retval = + htarget \
                 + dx \
                 - dx*(dx   //htarget   //TAU) \
                 + dx*(dx**2//htarget**2//TAU**2//2) \
                 + dx*(dx**3//htarget**3//TAU**3//6) \
                 - dx*(dx**4//htarget**4//TAU**4//24) \
                 + dx*(dx**5//htarget**5//TAU**5//120) \
                 - dx*(dx**6//htarget**6//TAU**6//720)
        if self.nodeid == 0:
            print(f"RETARGET node {self.nodeid:2} Adev={Adev:3} from {print_hash(self.target)} ... "
                  f"x = {print_hash(x0)}... {print_hash(retval)}... ")
        return retval

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
        self.target = network.target # Actual target gets filled in by tick() after cohorts are computed

    def __gt__(self, other):
        """ Create a > function which compares beads (for lexical ordering by hash value) """
        return self.hash > other.hash

    def __int__(self):
        return self.hash

    def __str__(self):
        return f"<Bead ...{self.hash%100000000}>"

    def add_PoW(self, hash):
        """ Add proof of work hash after it is computed. """
        self.hash = hash

class Braid:
    """ A Braid is a Directed Acyclic Graph with no incest (parents may not also
        be non-parent ancestors).  A braid may have multiple tips. Test case files
        may be loaded from a JSON file created by `save_braid()` for display and
        examination purposes.
    """

    def __init__(self, beads=None, filename=None, parents=None):
        self.beads    = {}      # A hash map of hashes of all beads for quick lookup
        self.times    = {}      # Time of arrival for each bead
        self.tips     = set()   # A tip is a bead with no children.
        self.cohorts  = []      # A running tally of cohorts # FIXME extending this list is probably causing nonlinear runtime

        if beads:
            for b in beads:
                self.beads[b.hash] = b
                self.tips.add(b)
                for p in b.parents:
                    self.times[b.hash] = b.t
                    if p in self.tips:
                        self.tips.remove(p)
            self.cohorts = list(braid.cohorts(dict(self)))
        elif filename or parents:
            if filename:
                dag      = braid.load_braid(filename)
            if parents:
                dag      = braid.make_dag(parents)
            network  = Network(nnodes=1, npeers=0) # Create a dummy network with one node
            for bead_hash in dag["parents"]:
                self.beads[bead_hash] = Bead(bead_hash, set(), network, network.nodes[0])
            for bead_hash, parent_hashes in dag["parents"].items():
                self.beads[bead_hash].parents = set(self.beads[p] for p in parent_hashes)
            self.tips = {self.beads[bead_hash] for bead_hash in dag["tips"]}
            self.cohorts = [{self.beads[bead_hash] for bead_hash in c} for c in dag["cohorts"]]

    def __iter__(self):
        """ You can dump a representation of a braid as a python dictionary like:
            dict(b), which uses this iterator. The result will contain <Bead> objects
            which you can cast to int, or use `braid.number_beads()` to assign new
            numbers for display purposes.

            Given an instance of Braid `b`, the parents map using hashes instead of
            Bead objects is obtained using the Bead.__int__ cast:
                hashed_parents = {int(k): set(map(int, v)) for k,v in dict(b).items()}
            A more display-friendly format can be obtained as:
                parents = braid.number_beads(hashed_parents)
        """
        for h, b in self.beads.items():
            yield b, set(p for p in b.parents if p.hash in self.beads)

    def __contains__(self, bead):
        return bead.hash in self.beads

    def parents(self):
        """ Return a dict of {bead: {parents}} for this braid, for use with the
            functions in braid.py.
        """
        return {b: set(p for p in b.parents) for b in self.beads.values()}

    def extend(self, bead, cohort_cache=None, compute_cohorts=True):
        """ Add a bead to the end of this braid. Returns True if the bead
            successfully extended this braid, and False otherwise.

            <bead> is a data structure from another node, and objects referenced by it in e.g.
            parents won't necessarily be the same object as this node has, so we have to check
            everything by hash and use our own objects.

            Arguments:
                bead:               A Bead object
                compute_cohorts:    If True, compute cohorts for the difficulty adjustment algorithm
            Returns:
                True if the bead was successfully added, False otherwise
        """
        if (not bead.parents                                           # No parents: bad block
                or not all(p.hash in self.beads for p in bead.parents) # Don't have all parents
                or bead.hash in self.beads):                           # Already seen this bead
            return False
        self.beads[bead.hash] = bead
        self.times[bead.hash] = bead.t
        self.tips            -= bead.parents
        self.tips.add(bead)

        # Find earliest parent of <bead> in cohorts and nuke all cohorts after that.
        if compute_cohorts:
            found_parents = set()
            dangling      = set([bead])
            for c in reversed(self.cohorts): # <bead> is never going to be in my cohorts
                found_parents |= set(p for p in bead.parents) & c
                dangling |= self.cohorts.pop()
                if len(found_parents) == len(bead.parents):
                    break
            frozen_dangling = frozenset(dangling)
            if cohort_cache is not None and frozen_dangling in cohort_cache:
                if DEBUG:
                    print(f"    Using cached cohorts for dangling set {print_hash(frozen_dangling)}")
                self.cohorts.extend(cohort_cache[frozen_dangling])
            else:
                # Construct a sub-braid from dangling and compute any new cohorts
                sub_braid = {d: set(p for p in d.parents if p in dangling) for d in dangling}
                # pass cohort_cache to cohorts() which will use it as an ancestor cache
                new_cohorts = list(braid.cohorts(sub_braid,
                                                 ancestor_cache=cohort_cache))
                if cohort_cache is not None:
                    cohort_cache[frozen_dangling] = new_cohorts
                    # Purge old cohorts and ancestors from the cache
                    if len(cohort_cache) > MAX_CACHE:
                        for _ in range(len(cohort_cache)-MAX_CACHE):
                            cohort_cache.popitem(last=False)

                self.cohorts.extend(new_cohorts)
                if DEBUG:
                    print(f"    Computed new cohorts: ", print_hash(new_cohorts))

        return True

    def print_cohorts(self):
        print("    cohorts:  ", [set(self.beads.index(b) for b in c) for c in self.cohorts])

    def plot(self, filename=None):
        def add_arrow(ax, source, target, markersize, arrow_head_width=0.4, arrow_head_length=0.5, linewidth=0.3):
            distance = sqrt((target[0] - source[0])**2 + (target[1] - source[1])**2)
            offset = 1.5*markersize/ax.figure.dpi # Adjust this value as needed to keep arrows from overlapping beads, esp if you change DPI
            dx = (target[0] - source[0]) / distance
            dy = (target[1] - source[1]) / distance
            ax.annotate("", xytext=(source[0]+dx*offset, source[1]+dy*offset), xy=(target[0]-dx*offset, target[1]-dy*offset),
                        arrowprops = {'arrowstyle': '->', 'linewidth': linewidth})

        bead_color          = ( 27/255, 158/255, 119/255, 1)    # Greenish
        genesis_color       = (217/255,  95/255,   2/255, 1)    # Orangeish
        cohort_color        = (117/255, 112/255, 179/255, 1)    # Purplisha
        tip_color           = (231/255,  41/255, 138/255, 1)    # Pinkish
        sibling_color       = (102/255, 166/255,  30/255, 1)    # Light Greenish
        # A rotating color palette to color cohorts
        color_palette = [genesis_color, cohort_color, sibling_color, tip_color]
        markersize          = 16

        # Create a graph
        fig, ax  = plt.subplots()

        # Construct basic braid objects with integer identifiers
        parents  = braid.number_beads({int(k): set(map(int, v)) for k,v in dict(self).items()})
        children = braid.reverse(parents)
        cohorts  = list(braid.cohorts(parents, children))
        hwpath   = braid.highest_work_path(parents, children)
        layouts  = []
        tips_pos = {} # stores positions of the tips from the previous cohort
        # layout() now returns the positions of beads as well as positions of tips required for placing the beads in the next cohort.
        for c in cohorts:
            layout, tips_pos = braid.layout(c, parents, None, tips_pos)
            layouts.append(layout)
        layout   = {}
        startx   = 0
        # Put all cohorts together in one layout map
        for cohort_layout, cohort_num in zip(layouts, range(len(cohorts))):
            for b, (x,y) in cohort_layout.items():
                layout[b] = (x+startx, y)
            startx += max([x for x,y in cohort_layout.values()]) + 1

        # Plot nodes
        for cohort, i in zip(cohorts, range(len(cohorts))):
            for bead in cohort:
                x,y = layout[bead]
                ax.plot(x, y, 'o', markersize=markersize, markerfacecolor=color_palette[i % len(color_palette)],
                        markeredgecolor='black', markeredgewidth=0.5)
                va_position = 'center' if y < 0 else 'center_baseline'
                ax.text(x, y, str(bead), ha='center', va=va_position, color='white', fontsize=10, fontweight='bold')

        # Plot edges (arrows)
        for node, parent_set in parents.items():
            for parent in parent_set:
                if parent in layout and node in layout:
                    x1, y1 = layout[parent]
                    x2, y2 = layout[node]
                    if node in hwpath and parent in hwpath:
                        add_arrow(ax, layout[node], layout[parent], markersize, linewidth=1.5)
                    else:
                        add_arrow(ax, layout[node], layout[parent], markersize, linewidth=0.5)
        ax.set_aspect('equal')
        ax.set_ylim(min(y for x,y in layout.values())-0.5, max(y for x,y in layout.values())+0.5)
        plt.axis('off')
        plt.tight_layout()
        if filename:
            plt.savefig(filename)
        else:
            plt.show()

def main():
    """ Main function so it doesn't make a bunch of globals. """
    global NETWORK_HASHRATE, TARGET_NB, TARGET_NC, TARGET_DAMPING, DEBUG
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
    parser.add_argument("-M", "--test-mining", action=BooleanOptionalAction,
        help="Test mining vs no-mining mode",
        default=False)
    parser.add_argument("-R", "--target-ratio",
        help="Target N_B/N_C ratio",
        default=f"{TARGET_NB}/{TARGET_NC}")
    parser.add_argument("-s", "--random-seed",
        help="Random seed (to regenerate the same network)",
        default=1)
    parser.add_argument("-D", "--damping-factor",
        help="Damping factor for difficulty adjustment",
        default=TARGET_DAMPING)
    parser.add_argument("-A", "--algorithm",
        help="Select the Difficulty Algorithm ('fixed', 'exp', 'parents', 'simple', 'pid', 'model', 'simple_asym', "
             "'simple_asym_damped')",
        default="exp")
    parser.add_argument("-l", "--log", action=BooleanOptionalAction,
        help="Log each bead as it is found to make plots.", default=False)
    parser.add_argument("--debug", action=BooleanOptionalAction,
        help="Print extra debugging information", default=False)
    args = parser.parse_args()
    DEBUG = args.debug
    if DEBUG: args.log = True
    TARGET_NB, TARGET_NC = map(int, re.search(r"(\d+)/(\d+)", args.target_ratio).groups())
    TARGET_DAMPING = int(args.damping_factor)
    random.seed(int(args.random_seed))

    print(f"# Simulating a global network of {args.nodes} nodes having {args.peers} peers each,")
    print(f"# targeting N_B/N_C = {TARGET_NB}/{TARGET_NC} and damping factor {TARGET_DAMPING},")
    print(f"# with hashrate {NETWORK_HASHRATE/args.nodes/NETWORK_SIZE/1000:5.4} kh/s per node, and target 2**{args.target}-1")
    print(f"# Using {args.algorithm} difficulty targeting algorithm")
    if args.mine:
        start = time.process_time()
        N_HASHES = 10000 # number of hashes to compute for benchmarking purposes
        for nonce in range(N_HASHES):
            sha256d(nonce)
        stop = time.process_time()
        print(f"# Network hashrate (single core) benchmark: {int(N_HASHES/(stop-start)/1000)} kh/s")
        NETWORK_HASHRATE = N_HASHES/(stop-start)
        bead_time     = MAX_HASH/(2**int(args.target)-1)/NETWORK_HASHRATE
        print(f"# We should generate a bead roughly once every {bead_time*1000:{8}.{6}}ms")
        print(f"# Expected time to completion: {bead_time*OVERHEAD_FUDGE*int(args.beads):{8}.{4}}s "
              f" to mine {args.beads} beads")
    else:
        print("# Using the geometric distribution to simulate mining.")

    target = 2**int(args.target)-1
    n = Network(int(args.nodes), NETWORK_HASHRATE, target=target, target_algo=args.algorithm, npeers=int(args.peers),
                log=args.log)
    if args.test_mining:
        n.simulate(nbeads=int(args.beads), mine=True)
        bmine   = copy(n.nodes[0].braid)
        mined_parents = {int(k): set(map(int, v)) for k,v in dict(bmine).items()}
        dag = braid.save_braid(mined_parents, args.filename+"-mine.json", args.description)
        Nc = len(dag['cohorts'])
        Ncerr = 1/sqrt(Nc)
        print(f"\n   mined Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}} +/- {Ncerr:{5}.{4}}")
        print(f"Wrote {len(bmine.beads)} beads to {args.filename}-mine.json.")
        n.reset(target)
        n.simulate(nbeads=int(args.beads), mine=False)
        bnomine = copy(n.nodes[0].braid)
        nomine_parents = {int(k): set(map(int, v)) for k,v in dict(bnomine).items()}
        dag = braid.save_braid(parents, args.filename+"-no-mine.json", args.description)
        Nc = len(dag['cohorts'])
        Ncerr = 1/sqrt(Nc)
        print(f"\nno-mined Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}} +/- {Ncerr:{5}.{4}}")
        print(f"Wrote {len(bnomine.beads)} beads to {args.filename}-no-mine.json.")
    else:
        n.simulate(nbeads=int(args.beads), mine=bool(args.mine))
        b = copy(n.nodes[0].braid)
        parents = {int(k): set(map(int, v)) for k,v in dict(b).items()}
        dag = braid.save_braid(parents, args.filename+".json", args.description)
        Nc = len(dag['cohorts'])
        Ncerr = 1/sqrt(Nc)
        print(f"\n# no-mined Nb/Nc = {len(dag['parents'])/len(dag['cohorts']):{8}.{4}} +/- {Ncerr:{5}.{4}}")
        print(f"# Wrote {len(b.beads)} beads to {args.filename}.json having {Nc} cohorts.")

if __name__ == "__main__":
    main()
