# Braid Consensus

Herein we describe the Braid consensus mechanism, which is a generalization of
Nakamoto consensus to a Directed Acyclic Graph (DAG).

## Braid Structure

The Braid is a DAG structure where each node (bead) may have one or more
parents. It has one additional rule ("no incest") that one cannot name an
ancestor of a parent as a parent. This eliminates sub-graphs that contain
triangles. The reason for this extra rule is that there is no additional
information conveyed by naming a higher-order ancestor as a parent. Parents of
parents (and all other ancestors) are already considered.

An example of a "thin" braid is:

[thin-braid]: thin_braid.png
![Thin Braid][thin-braid]

Here time is increasing as we move right.  The "no incest" rule means that for
example, beads 8 and 9 cannot name beads 0-6 as direct parents. The colors
correspond to "cohorts" which are sub-graphs separated by graph cuts. A graph
cut is a line drawn through the graph where *all* beads on the right side of the
cut have *all* beads on the left side of the cut as ancestors. The braid tip in
this example is the bead (10), which is expected be named as the sole ancestor
by a miner starting from this graph state.

An example of a "thick" braid is:

[thick-braid]: thick_braid.png
![Thick Braid][thick-braid]

In this image we can see an example of a higher order graph cut between cohort
(1,2,3) and cohort (4,5,6,7,8). The tips in this case are the beads (40,41),
both of which should be named as parents of a miner starting from this graph
state.

Graph cuts can be found with high speed using a depth first search and the
[Lowest Common Ancestor](https://en.wikipedia.org/wiki/Lowest_common_ancestor)
algorithm, which can be computed in linear time.

## Braid Mathematics

The production of Proof of Work shares is a Poisson process, given by the
Poisson probability mass function

$$
P(k) = \frac{(\lambda a)^k e^{\lambda a}}{k!}
$$

where the parameter $\lambda$ is the total hashrate of the network having units
[hashes/second] and $a$ is a global latency parameter having units [seconds].

For any subgraph corresponding to a length of time $T$, we can *measure* the
number of beads $N_B$, the number of cohorts $N_C$ as well as the average time
per bead $T_B = T/N_B$ and average time per cohort $T_C = T/N_C$. Finally the
quantity $x$ is the "target difficulty" representing the maximum acceptable
value for a proof of work hash.

The cohort time $T_C$ is easy to understand in the two limits $x\to0$ (high
difficulty - blockchain-like) and $x\to \infty$ (low difficulty - thick braid).
In the $x\to0$ limit, no beads have multiple parents, and each bead is a cohort.
The cohort time is then:

$$
T_C|_{x\to0} = T_B = \frac{1}{\lambda x}.
$$

In the opposite limit, in order to form a cohort, no beads must be produced
within a time approximately $a$ such that all beads have time to propagate to
other nodes, and be named as parents for the next bead(s), creating a cohort.
The probability that no beads are created within a time interval $a$ is given by

$$
P(0) = e^{-\lambda a}
$$

leading to a cohort time

$$
T_C|_{x\to\infty} = \frac{a}{P(0)} = a e^{\lambda a}
$$

Taken together, an extremely precise fit for the cohort time is given by the sum
of these two contributions which is shown in the green line in the graph below.

$$
T_C = \frac{1}{\lambda x} + a e^{a\lambda x}
$$

![Cohort Time vs target difficulty](T_C_x.png)

The exact behavior of the graph near the minimum is a function of the exact
network topology and inter-node latencies, and one can expect there to be some
"wiggles" in this graph near the minimum. The location of the minimum is given
by

$$
x_0 = \frac{2 W\left(\frac12\right)}{a\lambda} \simeq \frac{0.7035}{a \lambda}
$$

where $W(z)$ is the [Lambert W function](https://en.wikipedia.org/wiki/Lambert_W_function).

This value $x_0$ represents having the most-frequent consensus points within a
global network having a latency parameter $a$. Given the shallow trough at the
minimum, it may be desirable to consider a slightly higher target in order to
increase the bead rate and capture more shares within a window of time. But the
above analysis indicates that there's a hard exponential wall in how high we can
make the difficulty before the system fails to function.

## Consensus

Given a bead with $n$ parents $\{p_i\}$, $i=1..n$, any computable quantity
$f(\{p_i\})$ can be decided simply by examining the parents $p_i$ and their
ancestors. Thus just as in Bitcoin, any state can be determined solely by
knowing the braid tips.

The majority of consensus considerations in Bitcoin are regarding acceptable
transactions. As the first version of Braidpool will not have transactions, that
leaves the target difficulty for shares as the only quantity that needs to be
decided by consensus, which we describe how to compute below.

### Difficulty Adjustment

It is necessary to rate-limit shares. Since shares are broadcast to all nodes,
if the bead rate is too high, the communications complexity of sending all
shares with $N$ miners is $\mathcal{O}(N^2)$, which can easily be too much
bandwidth to handle.  Furthermore, if the bead rate is too high, one can
effectively never have graph cuts. This is because in order for a graph cut to
occur, the network must be quiescent for a time proportional to $a$.

When a miner starts mining, he chooses all available tips (beads with no
descendants) and names them as parents of his new share. He then traverses the
graph going back a time $T$ to compute $N_B$, and $N_C$. He then computes the parameters $\lambda$ and $a$ (which are different for *each* bead) as

$$
\lambda = \frac{N_B}{x T}, \qquad a = \frac{T}{N_C} W\left(\frac{N_C}{N_B}-1\right).
$$

The required difficulty for his bead which then given by $x_0$. This difficulty
is committed to in the [committed metadata]() and verified to be correct
according to the DAG and parent beads by all nodes.

### Critical Damping

In the event of a hashrate increases or decreases, the above difficulty
adjustment will tend to oscillate around the true value of the hashrate
$\lambda_0$ with a period of $2T$. Correspondingly the target $x(t)$ that we
calculate from the above will tend to oscillate around the desired value $x_0$.
We will damp these oscillations using [critical
damping](https://en.wikipedia.org/wiki/Damping), which means that the damping
factor is $\tau = T/\pi$. The resultant hashrate returns as quickly as possible
to the true value without oscillating. The resultant target behaves as a
critically damped oscillator:

$$
    x(t) = x_0 + (x_1-x_0) e^{-\pi t/T} \cos\left(\frac{\pi t}{T}\right)
$$

where $x_0$ is the new target in the absence of damping and $x_1$ is the last
target (which is taken to be the average target of the parents to a bead).  The
factor $e^{-\pi t/T}$ will go into our difficulty adjustment algorithm, and the
$\cos\left(\frac{\pi t}{T}\right)$ term comes from the natural behavior after a
change in hashrate. The value $t$ is the expected time to the next bead.

### Averaging Window

The last remaining free parameter in this algorithm is the averaging window $T$.
We want this to be short enough that it responds to changes in the network
hashrate on a timescale similar to that change, and long enough to average over
those in a reasonable manner. The change in the network hashrate is just its
time derivative $\lambda^\prime(t)$ which can be measured from the network.

FIXME more details and explicit formula

### Final Difficulty Adjustment Formula

Taking into account all of the above, the difficulty adjustment formula is then
given by first computing the desired time window $T$, counting $N_B$ and $N_C$
within that window, and then computing:

$$
\begin{array}{rcll}
\overline x       &=& \displaystyle \left(\frac{1}{N_B} \sum_{i \in {\rm beads}} \frac{1}{x_i} \right)^{-1}   & {\rm average\ target} \\[1.5em]
\overline \lambda &=& \displaystyle \frac{N_B}{\overline x T} & {\rm average\ hashrate} \\[1.5em]
a                 &=& \displaystyle \frac{T}{N_C} W\left(\frac{N_C}{N_B}-1\right) & {\rm latency\ parameter} \\[1.5em]
\overline x_1     &=& \displaystyle \left(\frac{1}{N_p} \displaystyle \sum_{p \in {\rm parents}} \frac{1}{x_p}\right)^{-1} & {\rm average\ parental\ target} \\[1.5em]
x_0               &=& \displaystyle \frac{2 W\left(\frac12\right)}{a \overline \lambda} & {\rm optimal\ target} \\[1.5em]
x                 &=& \displaystyle x_0 + (\overline x_1 - x_0) e^{-\pi a/T} & {\rm damped\ target}
\end{array}
$$

where the index $i$ ranges over all beads within the time window $T$, and the
index $p$ ranges over parents to this bead.

FIXME is $a$ correct in the last formula?

#### Difficulty Discussion

Each bead has a different difficulty which is independently computable by all
nodes, and when a share is broadcast, this is verified as a consensus
requirement for the share to be valid.

This algorithm automatically adjusts without any further coordination. If the
bead rate is low and the DAG is blockchain-like, it increases the target (lowers
the difficulty) which increases the bead rate. Likewise if the bead rate is
high, it decreases the target (raises the difficulty) which lowers the bead
rate. It does this without oscillating due to critical damping.

The only thing left to be decided now are edge cases where there are no cohorts
containing more than one bead, or where a cohort has not been formed in a long
time, or where there are no beads at all (because the system just started).

### Consensus on Other Quantities

For other information that may be contained within beads about which we wish to
reach consensus we require that:

* Children must not have information that conflicts with their parents.
* Beads which are not ancestors of one another *may* contain conflicting
  information (for instance, a double-spend).

Consensus points occur at graph cuts (cohort boundaries).  Because of the above
rules, it is only necessary to decide between conflicting information *within* a
cohort. For example, in the [thin braid](#thinbraid) example, beads (8) and (9)
can contain conflicting information, the resolution of which is decided by a
"merge" rule in the parent bead that ties them together. In Nakamoto consensus
this "merge" rule is work weighting where work $w=1/x$ in terms of the target
difficulty $x$.  In the event that (8) and (9) have exactly the same work, the
bead with the smaller hash is chosen. (a.k.a. "luck") In the event that the
cohort is more complex, descendant work must be taken into account. This is
given by a simple sum of descendant work for bead $i$:

$$
w_i = \frac{1}{x_i} + \sum_{d \in {\rm descendants}} \frac{1}{x_d}
$$

where the bead with the larger work value is preferred to resolve conflicting
information, and the sum need only be carried out until the next cohort
boundary, since by the definition of cohorts, all additional work after the
cohort boundary is added to the work of *all* potentially conflicting beads and
does not affect conflict resolution, and DAGs don't fork.

## Byzantine Broadcast

FIXME Discuss Radpool proposal and it's total lack of rate-limiting.
