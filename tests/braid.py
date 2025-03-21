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
    dag["bead_work"]         = bead_work if bead_work else {b:FIXED_BEAD_WORK for b in dag["parents"]}
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
            for t in tail:                   # Find all ancestors of all beads in the tail
                if t not in ancestors:
                    all_ancestors(t, parents, ancestors) # half the CPU time is here

            # Calculate cohort
            cohort = set()
            for a in ancestors:
                cohort |= ancestors[a]       # Union all ancestors with the cohort

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
    in_cohorts      = reversed(in_cohorts) if in_cohorts else cohorts(children)
    retval          = {} # The cumulative work for each bead
    for c in in_cohorts:
        sub_children    = sub_braid(c, children)   # children dict within the cohort
        sub_descendants = {}                       # descendants within the cohort
        for b in c:
            all_ancestors(b, sub_children, sub_descendants)
            retval[b] = previous_work + bead_work[b] + sum(bead_work[a] for a in sub_descendants[b])
        # All beads in the next cohort have ALL beads in this cohort as descendants.
        previous_work += sum(bead_work[b] for b in c)
    return retval

def bead_cmp(a, b, dwork, awork=None):
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
    if a > b:                   # same work, fall back on lexical order
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

def highest_work_path(parents, children=None, work=None, bead_work=None):
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

def layout(cohort, all_parents, all_children=None, bead_work=None):
    """
    Places beads on a grid based on DAG structure and highest work path.

    Args:
        all_parents (dict): Dictionary mapping bead to a set of its parents.
        all_children (dict): Dictionary mapping bead to a set of its children.

    Returns:
        dict: Dictionary mapping bead to its (x, y) coordinates on the grid.

    FIXME will draw lines over other beads when a bead is in both the head and tail.
    """

    all_children  = all_children if all_children else reverse(all_parents)
    bead_work = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in all_parents}

    # Get the sub-DAG for this cohort.
    parents  = dict(sub_braid(cohort, all_parents).items())
    children = reverse(parents)
    hwpath   = highest_work_path(parents, children, bead_work=bead_work)
    head     = cohort_head(cohort, parents, children)
    tail     = cohort_tail(cohort, parents, children)

    # Assign x-coordinates to hwpath beads initially
    x_coords = {}
    for i, bead in enumerate(hwpath):
        x_coords[bead] = i

    # Assign x-coordinates to remaining beads using a topological sort
    visited = set()

    def get_x_coord(bead):
        if bead in x_coords:
            return x_coords[bead]

        if bead in visited:
            return x_coords[bead]

        # Special case: beads with no parents should be at x=0
        if bead in head:
            min_x = 0
        else:
            # Determine the minimum x-coordinate based on parents
            min_x = 0
            for parent in parents.get(bead, set()):
                # Handle parent-child relationship issues
                parent_x = get_x_coord(parent)
                min_x = max(min_x, parent_x + 1)  # Ensure at least 1 unit to the right

        # Determine the maximum x-coordinate based on children
        # This is a soft constraint - we'll try to respect it but parent constraints take priority
        max_x = float('inf')
        for child in children.get(bead, set()):
            if child in x_coords:
                max_x = min(max_x, x_coords[child] - 1)

        if min_x > max_x and max_x < float('inf'):
            # Constraint conflict - parent and child constraints can't both be satisfied
            for child in children.get(bead, set()):
                if child in x_coords and x_coords[child] <= min_x:
                    # Shift this child and all beads to its right
                    shift_amount = min_x + 1 - x_coords[child]
                    for other_bead in x_coords:
                        if x_coords[other_bead] >= x_coords[child]:
                            x_coords[other_bead] += shift_amount
            x_coords[bead] = min_x
        else:
            x_coords[bead] = min_x

        visited.add(bead)

        return x_coords[bead]

    # Try to assign coordinates to all beads
    for bead in parents.keys():
        if bead not in x_coords and bead not in visited:
            get_x_coord(bead)

    # find the maximum x-coordinate
    max_x = max(x_coords.values()) if x_coords else 0

    # Adjust beads with no children to be at the right edge
    for bead in tail:
        if bead not in hwpath:  # Don't override hwpath coordinates
            x_coords[bead] = max_x

    # Fix any remaining issues
    for bead in parents.keys():
        if bead not in x_coords:
            # If we couldn't assign a position, find a reasonable one
            parent_xs = [x_coords.get(p, 0) for p in parents.get(bead, set()) if p in x_coords]
            child_xs = [x_coords.get(c, max_x) for c in children.get(bead, set()) if c in x_coords]

            if parent_xs and child_xs:
                max_parent_x = max(parent_xs)
                min_child_x = min(child_xs)
                if max_parent_x < min_child_x - 1:
                    x_coords[bead] = max_parent_x + 1
                else:
                    # Place it at the average of parent and child positions
                    x_coords[bead] = (max_parent_x + min_child_x) // 2
            elif parent_xs:
                x_coords[bead] = max(parent_xs) + 1
            elif child_xs:
                x_coords[bead] = min(child_xs) - 1
            else:
                # Isolated bead, place it at 0
                x_coords[bead] = 0

    # Adjust hwpath beads to maintain relative positions if needed
    hwpath_left = min(x_coords[bead] for bead in hwpath)
    hwpath_offset = 0
    if hwpath_left > 0:
        hwpath_offset = -hwpath_left

    # Shift all coordinates to ensure beads with no parents are at x=0
    min_x = min(x_coords.values())
    if min_x > 0:
        offset = -min_x
        for bead in parents.keys():
            x_coords[bead] += offset

    # Assign y-coordinates
    positions = {}

    # Place hwpath beads at y=0
    for bead in hwpath:
        positions[bead] = (x_coords[bead] + hwpath_offset, 0)

    # Ensure consistency for hwpath coordinates
    for i in range(len(hwpath) - 1):
        if positions[hwpath[i]][0] >= positions[hwpath[i+1]][0]:
            positions[hwpath[i+1]] = (positions[hwpath[i]][0] + 1, 0)

    # Update x_coords for hwpath beads to match positions
    for bead in hwpath:
        x_coords[bead] = positions[bead][0]

    # Process remaining beads in order of their x-coordinate
    remaining_beads = sorted([b for b in parents.keys() if b not in hwpath], key=lambda b: x_coords[b])

    def intersection(x1, y1, x2, y2, x3, y3):
        """ Check if the point (x3, y3) lies on the line segment from (x1, y1) to (x2, y2) """
        if (x2 - x1) * (y3 - y1) == (y2 - y1) * (x3 - x1):
            if min(x1, x2) <= x3 <= max(x1, x2) and min(y1, y2) <= y3 <= max(y1, y2):
                return True
        return False

    # Place remaining beads in work sorted order (lowest work at top)
    for bead in sorted(remaining_beads, key=work_sort_key(parents, children, bead_work), reverse=True):
        x = x_coords[bead]
        y = 1  # Start with y=1 (above hwpath)

        while True:
            valid = True

            # Check if position (x, y) is already occupied
            for other_bead, (other_x, other_y) in positions.items():
                if other_x == x and other_y == y:
                    valid = False
                    break

            if not valid:
                y += 1
                continue

            # Check if any existing edge passes through the new bead's position
            for parent_bead, (parent_x, parent_y) in positions.items():
                for child_bead in children.get(parent_bead, set()):
                    if child_bead in positions:
                        child_x, child_y = positions[child_bead]
                        if intersection(parent_x, parent_y, child_x, child_y, x, y):
                            valid = False
                            break
                if not valid:
                    break

            # Check if any edge from the new bead to its parents or children passes through any existing bead
            for parent in parents.get(bead, set()):
                if parent in positions:
                    parent_x, parent_y = positions[parent]
                    for other_bead, (other_x, other_y) in positions.items():
                        if other_bead != parent and other_bead != bead:
                            if intersection(parent_x, parent_y, x, y, other_x, other_y):
                                valid = False
                                break
                if not valid:
                    break

            if not valid:
                y += 1
                continue

            for child in children.get(bead, set()):
                if child in positions:
                    child_x, child_y = positions[child]
                    for other_bead, (other_x, other_y) in positions.items():
                        if other_bead != child and other_bead != bead:
                            if intersection(x, y, child_x, child_y, other_x, other_y):
                                valid = False
                                break
                if not valid:
                    break

            if valid:
                break

            y += 1

        positions[bead] = (x, y)

    return positions

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

class TestCohortMethods(unittest.TestCase):
    """ Test harness for unittest. """
    parents1 = {0:set(), 1:{0}, 2:{1}, 3:{2}} # blockchain
    parents2 = {0:set(), 1:set(), 2:{1}, 3:{1}}
    parents3 = {0:set(), 1:set(), 2:set(), 3:{1}, 4:{0}}
    parents4 = {0:set(), 1:set(), 2:set(), 3:{0,1,2}, 4:{0,1,2}, 5:{0,1,2}}
    diamond  = {0:set(), 1:{0}, 2:{0}, 3:{1,2}, 4:{3}}

    def test_geneses1(self):
        self.assertEqual(geneses(self.parents1), {0})

    def test_geneses2(self):
        self.assertEqual(geneses(self.parents2), {0, 1})

    def test_geneses3(self):
        self.assertEqual(geneses(self.parents3), {0, 1, 2})

    def test_geneses_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            self.assertEqual(geneses(dag["parents"]), {0})

    def test_tips1(self):
        parents1 = {0:set(), 1:[0], 2:[1], 3:[2]}
        self.assertEqual(tips(parents1), {3})

    def test_tips2(self):
        parents2 = {0:set(), 1:[0], 2:[1], 3:[1]}
        self.assertEqual(tips(parents2), {2,3})

    def test_tips3(self):
        parents3 = {0:set(), 1:set(), 2:set(), 3:[0,1,2], 4:[0,1,2], 5:[0,1,2]}
        self.assertEqual(tips(parents3), {3,4,5})

    def test_reverse(self):
        self.assertEqual(reverse(self.parents4),
                         {0: {3, 4, 5}, 1: {3, 4, 5}, 2: {3, 4, 5}, 3: set(), 4: set(), 5: set()})

    def test_cohorts(self):
        """ Test cohorts for a trivial blockchain-like braid. """
        self.assertEqual(list(cohorts(self.parents1)), [{0}, {1}, {2}, {3}])

    def test_cohorts_files(self):
        """ Test an assortment of example *.json files. """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            self.assertEqual(list(cohorts(dag["parents"])), dag["cohorts"])

    def test_cohorts_reversed_files(self):
        """ Does it find the same cohorts in the forward and backward directions? """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            p = reverse(dag["parents"])
            c = dag["cohorts"]
            c.reverse()
            self.assertEqual(list(cohorts(p)), c, msg="Test file: {filename}")

    def test_highest_work_path(self):
        self.assertEqual(highest_work_path(self.parents1, reverse(self.parents1)), [0,1,2,3])

    def test_higest_work_path_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            msg = f"Test file: {filename}"
            dag = load_braid(TEST_CASE_DIR+filename)
            self.assertEqual(highest_work_path(dag["parents"], dag["children"]), dag["highest_work_path"], msg=msg)

    def test_check_cohort_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            msg = f"Test file: {filename}"
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                self.assertEqual(check_cohort(c, dag["parents"], dag["children"]), True, msg=msg)

    def test_check_work_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            msg = f"Test file: {filename}"
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                self.assertEqual(dag["work"], descendant_work(dag["parents"], dag["children"], dag["bead_work"]),
                                    msg=msg)

    def test_sub_braid_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                msg = f"Test file: {filename}"
                self.assertEqual(geneses(sub_braid(c, dag["parents"])),
                                 cohort_head(c, dag["parents"], dag["children"]), msg=msg)
                self.assertEqual(tips(sub_braid(c, dag["parents"])),
                                 cohort_tail(c, dag["parents"], dag["children"]), msg=msg)
                self.assertEqual(list(cohorts(sub_braid(c, dag["parents"]))),
                                 [c], msg=msg)

    def test_head_tail_files(self):
        """ Test that cohort_head and cohort_tail do the same thing as geneses and tips. """
        for filename in sorted([filename for filename in
                                os.listdir(TEST_CASE_DIR) if
                                filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            for c in dag["cohorts"]:
                msg = f"Test file: {filename}"
                self.assertEqual(cohort_head(c, dag["parents"], dag["children"]),
                                 geneses(sub_braid(c, dag["parents"])), msg=msg)
                self.assertEqual(cohort_tail(c, dag["parents"], dag["children"]),
                                 tips(sub_braid(c, dag["parents"])), msg=msg)

    def test_all_ancestors(self):
        """ Test that the iterative and recursive definitions of all_ancestors match.
        """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".json")]):
            dag = load_braid(TEST_CASE_DIR+filename)
            for b in dag["parents"]:
                msg = f"Test file: {filename}"
                self.assertEqual(all_ancestors(b, dag["parents"]), all_ancestors_recursive(b, dag["parents"]), msg=msg)

if __name__ == "__main__":
    unittest.main()
