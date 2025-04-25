"""
    A set of tools for manipulating test braids. The algorithms herein are intended to work with any
    bead object supporting:
        Bead.__gt__ (for lexical ordering when PoW ordering fails)
        Bead.__int__ (for dumping to a file)
            # FIXME using __str__ to print bitcoin-BE hex encoding might be better...
    Since parents are always explicitly passed in, we don't depend on getting parents from the Bead
    object used.
"""

import json
import os
import unittest
from copy import copy
from collections import OrderedDict
from functools import cmp_to_key
from math import gcd
from bidict import bidict

TEST_CASE_DIR   = "braids/"
FIXED_BEAD_WORK = 1        # The work per bead if work is not passed.

def make_dag(hashed_parents, bead_work=None, description=None):
    """ Make a DAG object which caches the children, geneses, tips, cohorts,
        and highest work path.
    """
    parents                  = number_beads(hashed_parents)
    dag                      = {}
    dag["description"]       = description
    dag["parents"]           = parents
    dag["children"]          = reverse(parents)
    dag["geneses"]           = geneses(parents)
    dag["tips"]              = tips(parents, dag["children"])
    dag["cohorts"]           = list(cohorts(parents))
    dag["bead_work"]         = bead_work if bead_work else {b:FIXED_BEAD_WORK for b in dag["parents"]} # FIXME number_beads() above may have relabeled relative to what's in bead_work.
    dag["work"]              = descendant_work(parents, dag["children"], dag["bead_work"], dag["cohorts"])
    dag["highest_work_path"] = highest_work_path(parents, dag["children"], dag["work"])
    return dag

def geneses(parents):
    """ Given a dict of {bead: {parents}}, return the set of beads which have no parents. """
    retval = set()
    for b,p in parents.items():
        if not p:
            retval.add(b)
    return retval

def tips(parents, children=None):
    """ Given a dict of {bead: {parents}}, return the set of beads which have no children. """
    children = children if children else reverse(parents)
    return geneses(children)

def reverse(parents):
    """ Given a dict of {bead: {parents}}, compute the corresponding {bead: {children}} (or
        vice-versa).
    """
    children = {}
    for bead, bparents in parents.items():
        if bead not in children:
            children[bead] = set()

        for p in bparents:
            if p not in children:
                children[p] = set()
            children[p].add(bead)
    return children

def generation(beads, children=None):
    """ Given a set of <beads>, compute the set of all children of all {beads}.
        Call this with parents instead of children to move in the other direction.
    """
    retval = set()
    for b in beads:
        retval |= children[b]
    return retval

def all_ancestors_recursive(b, parents, ancestors={}):
    """ Gets all ancestors for a bead <b>, filling in ancestors of
        any other ancestors encountered, using a recursive
        algorithm.  Assumes b not in parents and b not in ancestors.
    """
    ancestors[b] = set(copy(parents[b]))
    for p in parents[b]:
        if p not in ancestors:
            all_ancestors(p, parents, ancestors)
        ancestors[b].update(ancestors[p])
    return ancestors

def all_ancestors(b, parents, ancestors={}):
    """ Gets all ancestors for a bead <b>, filling in ancestors of any other
        ancestors encountered, using an iterative algorithm. Assumes b not in
        parents and b not in ancestors.
    """
    work_stack = [(b, False)]  # (bead, is_processed)

    while work_stack:
        current, is_processed = work_stack[-1]

        if is_processed:
            # We've finished processing all parents, compute ancestors
            work_stack.pop()
            ancestors[current] = set(copy(parents[current]))

            # Update with ancestors of all parents
            for p in parents[current]:
                ancestors[current].update(ancestors[p])
        else:
            # Mark as being processed
            work_stack[-1] = (current, True)

            # Add any unprocessed parents to the stack
            for p in parents[current]:
                if p not in ancestors:
                    work_stack.append((p, False))

    return ancestors

def cohorts(parents, children=None, initial_cohort=None):
    """ Given the seed of the next cohort (which is the set of beads one step older, in the next
        cohort), build an ancestor/descendant set for each visited bead.  A new cohort is
        formed if we encounter a set of beads, stepping in the descendant direction, for which
        *all* beads in this cohort are ancestors of the first generation of beads in the next
        cohort.
    """
    children     = reverse(parents) if not children else children
    dag_tips     = tips(parents, children)
    cohort       = initial_cohort or geneses(parents)
    oldcohort    = set()
    head         = copy(cohort)
    tail         = copy(cohort)
    while True :
        ancestors = {h: set() for h in head} # Don't let head have ancestors to stop iteration
        cohort    = copy(head)               # Initial cohort is the head

        while True:                          # DFS search
            # Calculate new tail
            if not head:
                return                       # StopIteration and return
            for b in cohort-oldcohort:
                tail |= children[b]          # Add the next generation to the tail
            tail |= cohort ^ oldcohort       # Add any beads in oldcohort but not in cohort
            if cohort & dag_tips:            # If there are any tips in cohort, add tips to tail
                tail |= dag_tips-cohort
            else:
                tail -= cohort               # If there are no tips in cohort subtract off cohort

            oldcohort = copy(cohort)         # Copy so we can tell if new tail has changed anything
                                             # because changing the tail but not cohort may find
                                             # new ancestors

            # Calculate ancestors
            for t in tail - set(ancestors.keys()):   # Find all ancestors of all beads in the tail
                all_ancestors(t, parents, ancestors) # half the CPU time is here

            # Calculate cohort
            cohort = set.union(set(), *ancestors.values()) # Union all ancestors with the cohort

            # Check termination cases
            if dag_tips <= cohort:           # Cohort contains all tips
                head = set()                 # StopIteration and return
                break                        # and yield the current cohort
            if cohort and all(ancestors[t] == cohort for t in tail): # Standard cohort case
                head = copy(tail)            # Head of next cohort is tail from previous iteration
                break                        # Yield successful cohort
            if cohort == oldcohort:          # Cohort hasn't changed, we may be looping
                if dag_tips <= tail:         # Tail contains all tips but we didn't form a cohort
                    head = set()
                    cohort |= tail
                    tail = set()
                    break                    # Yield cohort+tail
                cohort.update(tail)
        oldcohort = set()
        yield cohort

def cohort_tail(cohort, parents, children=None):
    """ Given a cohort as a set of beads, compute its tail. If the tail intersects the tips,
        return all tips.
    """
    children = children if children else reverse(parents)
    return cohort_head(cohort, parents=children, children=parents)

def cohort_head(cohort, parents, children=None):
    """ Given a cohort as a set of beads, compute its head. If the tail intersects the geneses,
        return all geneses.
    """
    children    = children if children else reverse(parents)
    tail        = generation(generation(cohort, parents) - cohort, children)
    cohort_tips = geneses(parents)
    if not tail or any({t in cohort_tips for t in tail}):
        return cohort_tips
    return tail

def sub_braid(beads, parents):
    """ Given a set of <beads> (which generally will be a cohort), return the sub-DAG corresponding
        to only those beads. That is, compute the parents dict: {p: {children} for p in beads} such
        that the returned parents dict contains only the beads in <beads> and the parents of all
        beads are only those parents within <beads>.

        The result has the properties:
            geneses(sub_braid(beads, parents)) = cohort_head(beads, parents)
            tips(sub_braid(beads, parents)) = cohort_tail(beads, parents)
            cohorts(sub_braid(beads, parents)) == [beads]
    """
    return {b: {p for p in parents[b] if p in beads} for b in beads}

def descendant_work(parents, children=None, bead_work=None, in_cohorts=None):
    """ Find the work in descendants.  Work in ancestors can be found by reversing the order of
        parents and children:

            ancestor_work = descendant_work(children, parents)
    """
    children        = children if children else reverse(parents)
    bead_work       = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}
    previous_work   = 0
    rev_cohorts     = reversed(in_cohorts) if in_cohorts else cohorts(children)
    retval          = {} # The cumulative work for each bead
    for c in rev_cohorts:
        sub_children    = sub_braid(c, children)   # children dict within the cohort
        sub_descendants = {}                       # descendants within the cohort
        for b in c:
            all_ancestors(b, sub_children, sub_descendants)
            retval[b] = previous_work + bead_work[b] + sum(bead_work[a] for a in sub_descendants[b])
        # All beads in the next cohort have ALL beads in this cohort as descendants.
        previous_work += sum(bead_work[b] for b in c)
    return retval

def bead_cmp(a:int, b:int, dwork, awork=None):
    """ A custom cmp(b1,b2) function for sorting beads. This function requires the work function,
        which should be the output of descendant_work().

        In the event of a tie it resolves the tie in the following order:
        1. Highest descendant work
        2. Highest ancestor work
        2. FUTURE UNIMPLEMENTED: Lowest hash ("luck")
        3. FUTURE UNIMPLEMENTED: Earliest timestamp
        4. Lowest label (block hash) -- this is "earliest" in simulations

        Use this like:

            dwork = descendant_work(parents,children,bead_work)
            awork = descendant_work(children,parents,bead_work)
            cmp = lambda x,y: bead_cmp(x,y,dwork,awork)
            sort_key = cmp_to_key(lambda x,y: cmp(x,y))

            sorted(beads, key=sort_key)
    """
    if dwork[a] < dwork[b]:       # highest work
        return -1
    if dwork[a] > dwork[b]:
        return 1
    if awork:
        if awork[a] < awork[b]:
            return -1
        if awork[a] > awork[b]:
            return 1
    if a > b:                     # same work, fall back on block hash ("luck")
        return -1
    if a < b:
        return 1
    return 0

def work_sort_key(parents, children=None, bead_work=None):
    """ Return a sorting key lambda suitable to feed to python's min, max, sort etc. Note that
        sort() sorts values from lowest to highest. When using work_sort_key it will sort beads from
        lowest work to highest. Use `reverse=True` as an argument to sort() if you want the highest
        work, or reverse the resultant list.

        Use this like:
            sorted(beads, key=work_sort_key(parents))  # sorted from lowest work to highest
            max(beads, key=work_sort_key(parents))     # maximum work
            min(beads, key=work_sort_key(parents))     # minimum work
    """
    children = children if children else reverse(parents)
    bead_work = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}
    dwork = descendant_work(parents,children,bead_work)
    awork = descendant_work(children,parents,bead_work)
    return cmp_to_key(lambda a,b: bead_cmp(a,b,dwork,awork))

def highest_work_path(parents, children=None, bead_work=None):
    """ Find the highest (descendant) work path, by following the highest weights through the DAG.

        The highest *ancestor* work path can be found by calling with children and parents reversed:

            highest_work_path(children, parents)
    """
    children  = children if children else reverse(parents)
    bead_work = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}
    sort_key  = work_sort_key(parents, children, bead_work)
    hwpath    = [max(geneses(parents), key=sort_key)]

    while hwpath[-1] not in tips(parents, children):
        hwpath.append(max(generation({hwpath[-1]}, children), key=sort_key))
    return hwpath

def check_cohort(cohort, parents, children=None):
    """ Check a cohort using check_cohort_ancestors in both directions. """
    children = children if children else reverse(parents)
    return check_cohort_ancestors(cohort, parents, children) \
            and check_cohort_ancestors(cohort, children, parents)

def check_cohort_ancestors(cohort, parents, children=None):
    """ Check a cohort by determining the set of ancestors of all beads.  This computation is done
        over the ENTIRE DAG since any ancestor could have a long dangling path leading to this
        cohort.  This will not determine if a cohort has valid sub-cohorts since the merging of any
        two or more adjacent cohorts is still a valid cohort.

        This checks in one direction only, looking at the ancestors of `cohort`. To check in the
        other direction, reverse the order of the parents and children arguments.
    """
    children = children if children else reverse(parents)
    ancestors = {}
    allancestors = set()
    head = cohort_head(cohort, parents, children)
    for b in cohort:
        all_ancestors(b, parents, ancestors)
        allancestors |= ancestors[b]
    allancestors -= cohort
    if allancestors and generation(allancestors, children) - allancestors != head:
        return False
    return True

def layout(cohort, all_parents, bead_work=None, previous_cohort_tips=None):
    """
    Places beads on a grid based on DAG structure and highest work path. This
    algorithm operates on one <cohort> at a time.

    Args:
        cohort (set): Set of beads in the cohort.
        all_parents (dict): Dictionary mapping bead to a set of its parents.
        bead_work (dict): Dictionary mapping bead to its work.
        previous_cohort_tips (dict): Dictionary mapping bead to its y-coordinate in the previous cohort.

    Returns:
        dict, dict: Dictionary mapping bead and tip to its (x, y) coordinates on the grid.

    FIXME will draw lines over other beads when a bead is in both the head and tail.
    FIXME place beads both above and below the highest work path.
    """

    def intersection(x1, y1, x2, y2, x3, y3):
        """ Check if the point (x3, y3) lies on the line segment from (x1, y1) to (x2, y2) """
        if [x1,y1] == [x3,y3] or [x2,y2] == [x3,y3]: return False # Ignore duplicate endpoints
        return ((x2 - x1) * (y3 - y1) == (y2 - y1) * (x3 - x1) and
                min(x1, x2) <= x3 <= max(x1, x2) and
                min(y1, y2) <= y3 <= max(y1, y2))

    def set_x_coord(bead):
        """ Set an x-coordinate for a bead based on being right of its parents
            and left of its children.
        """
        nonlocal proposed_x
        if bead in proposed_x:
            return

        # Beads with no parents should be at x=0
        if bead in head:
            min_x = 0
        else: # Determine the minimum x-coordinate based on parents
            min_x = 0
            for parent in parents[bead]: # Handle parent-child relationship issues
                set_x_coord(parent)
                min_x = max(min_x, proposed_x[parent] + 1)

        # Determine the maximum x-coordinate based on children
        # This is a soft constraint - we'll try to respect it but parent constraints take priority
        max_x = float('inf')
        for child in children[bead]:
            if child in proposed_x:
                max_x = min(max_x, proposed_x[child] - 1)

        if min_x > max_x and max_x < float('inf'):
            # Constraint conflict - parent and child constraints can't both be satisfied
            for child in children[bead]:
                if child in proposed_x and proposed_x[child] <= min_x:
                    # Shift this child and all beads to its right
                    shift_amount = min_x + 1 - proposed_x[child]
                    for other in proposed_x:
                        if proposed_x[other] >= proposed_x[child]:
                            proposed_x[other] += shift_amount
        proposed_x[bead] = min_x

    # Get the sub-DAG for this cohort.
    all_children      = reverse(all_parents) # children dict of the whole braid
    prev_cohort_edges = {k: v for k, v in all_children.items() if k in previous_cohort_tips} if previous_cohort_tips else {} # extract connectivity with the tips of previous cohort
    parents           = dict(sub_braid(cohort, all_parents).items())
    children          = reverse(parents)
    hwpath            = highest_work_path(parents, children, bead_work=bead_work)
    head              = cohort_head(cohort, parents, children)
    tail              = cohort_tail(cohort, parents, children)
    bead_work         = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}

    # Assign x-coordinates to hwpath beads in order of decreasing work along the y=0 axis
    proposed_x = {bead: i for i, bead in enumerate(hwpath)}

    # Try to assign x coordinates to all beads based on being right of their parents and left of their children
    for bead in set(parents) - set(hwpath):
        set_x_coord(bead)

    # find the maximum x-coordinate
    max_x = max(proposed_x[bead] for bead in proposed_x)

    # Put beads with no children to be at the right edge
    for bead in set(tail) - set(hwpath):
        proposed_x[bead] = max_x

    # Ensure consistency for hwpath which may have moved due to parent-child relationships.
    for i, bead in enumerate(hwpath[:-1]):
        if proposed_x[bead] >= proposed_x[hwpath[i+1]]:
            proposed_x[hwpath[i+1]] = proposed_x[bead] + 1

    pos = {bead: [proposed_x[bead], 0] for bead in hwpath}
    lines = [] # A running tally of lines on the graph

    extended_children = copy(children)
    for key, value in prev_cohort_edges.items():
        if key not in children:
            extended_children[key] = set()
        extended_children[key] |= value
    extended_parents = reverse(extended_children)
    if previous_cohort_tips:
        for key, value in previous_cohort_tips.items():
            pos[key] = [-1, value[1]] # add the position of tips from the previous cohort as (-1, y_coord)
    # Place remaining beads in work sorted order (lowest work at top)
    for bead in sorted(set(parents) - set(hwpath),
                       key=work_sort_key(parents, children, bead_work), reverse=True):
        x = proposed_x[bead]
        y = 0
        dist = 0

        while True:
            dist += 1
            if y <= 0:
                y += dist
            else:
                y -= dist
            if [x,y] in pos.values(): continue

            # Create a list of all lines on the graph including the proposed <bead> position [x,y]
            pos[bead] = [x, y]
            new_lines = [(pos[parent], pos[child])
                          for parent, child in
                              [(bead, c) for c in extended_children[bead] if c in pos] +
                              [(p, bead) for p in extended_parents[bead] if p in pos]
                        ]

            # If there are no intersections of a parent-child edge with any middle bead, break
            if not any(intersection(*line[0], *line[1], *pos[middle]) for line in lines + new_lines
                       for middle in pos):
                break

        lines += new_lines
    cohort_tips = tips(parents, children)
    tips_pos = {tip: pos[tip] for tip in cohort_tips}
    return pos, tips_pos

def load_braid(filename):
    """ Load a JSON file containing a braid.
    """
    with open(filename, encoding="utf8") as json_data:
        d = json.load(json_data)
        dag = {}
        dag["description"]       = d["description"]
        dag["parents"]           = {int(k): set(v) for k,v in d["parents"].items()}
        dag["children"]          = {int(k): set(v) for k,v in d["children"].items()}
        dag["geneses"]           = set(d["geneses"])
        dag["tips"]              = set(d["tips"])
        dag["cohorts"]           = [set(map(int,c)) for c in d["cohorts"]]
        if "bead_work" not in d or d["bead_work"] is None:
            dag["bead_work"]     = {b:1 for b in dag["parents"]}
        else:
            dag["bead_work"]     = {int(k): v for k,v in d["bead_work"].items()}
        dag["work"]              = {int(k): v for k,v in d["work"].items()}
        dag["highest_work_path"] = d["highest_work_path"]

        json_data.close()
        return dag
    raise FileNotFoundError("load_braid could not open file: ", filename)

def number_beads(hashed_parents):
    """ Number the beads in a braid sequentially in topological order starting at genesis.  This is useful for test
        cases to not print huge hashes.
    """
    bead_id  = 0
    parents  = {}
    bead_ids = bidict() # a hash map from the bead identifier (a hash) to its (small) number and v/v
    for bead_hash in geneses(hashed_parents):
        bead_ids[bead_hash] = bead_id
        parents[bead_id]    = set()
        bead_id            += 1
    # Traverse the DAG in BFS in the descendant direction
    hashed_children = reverse(hashed_parents)
    next_parents = copy(parents)
    while next_parents:
        working_parents = copy(next_parents)
        next_parents    = {}
        for parent in working_parents:
            for bead_hash in hashed_children[bead_ids.inv[parent]]:
                this_id = bead_id
                if bead_hash not in bead_ids:
                    this_id = bead_ids[bead_hash] = bead_id
                    bead_id += 1
                else:
                    this_id = bead_ids[bead_hash]
                if this_id not in parents:
                    parents[this_id] = set()
                if this_id not in next_parents:
                    next_parents[this_id] = set()
                next_parents[this_id].add(parent)
                parents[this_id].add(parent)
    return parents

def save_braid(parents, filename, description=None):
    """ Save a JSON file containing a braid. It should contain the keys "description", "parents",
        "cohorts", and "workpath"
    """
    dag = make_dag(parents)
    with open(filename, 'w', encoding="utf8") as file:
        result = OrderedDict([
            ("description", description),
            ("parents", {int(bead): [int(p) for p in parents]
                         for bead,parents in dag["parents"].items()}),
            ("children", {int(bead): [int(c) for c in children]
                          for bead,children in dag["children"].items()}),
            ("geneses", [int(bead) for bead in dag["geneses"]]),
            ("tips", [int(bead) for bead in dag["tips"]]),
            ("cohorts", [sorted(list(map(int, c))) for c in dag["cohorts"]]),
            ("bead_work", {int(bead): work for bead,work in dag["bead_work"].items()}),
            ("work", {int(bead): work for bead,work in dag["work"].items()}),
            ("highest_work_path", [int(bead) for bead in dag["highest_work_path"]])
        ])
        file.write(json.dumps(result, sort_keys=False, indent=4))
        file.close()
    return dag

