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

def make_dag(parents, bead_work=None, description=None):
    """ Make a DAG object which caches the children, geneses, tips, cohorts,
        and highest work path.
    """
    dag                      = {}
    dag["description"]       = description
    dag["parents"]           = parents
    dag["children"]          = reverse(parents)
    dag["geneses"]           = geneses(parents)
    dag["tips"]              = tips(parents, dag["children"])
    dag["cohorts"]           = list(cohorts(parents))
    dag["bead_work"]         = bead_work if bead_work else {b:1 for b in dag["parents"]}
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

def all_ancestors(b, parents, ancestors):
    """ Gets all ancestors for a bead <b>, filling in ancestors of
        any other ancestors encountered, using a recursive
        algorithm.  Assumes b not in parents and b not in ancestors.
    """
    ancestors[b] = set(copy(parents[b]))
    for p in parents[b]:
        if p not in ancestors:
            all_ancestors(p, parents, ancestors)
        ancestors[b].update(ancestors[p])

def all_ancestors_iterative(b, parents, ancestors):
    """ Gets all ancestors for a bead <b>, filling in ancestors of any other ancestors
        encountered, using an iterative algorithm.
        FIXME broken
    """
    visited = {}
    pstack = [b]
    while pstack: # Loop 1: ensure we have parents of all ancestors
        current = pstack.pop()
        if current in parents:
            continue
        parents[current] = generation(current, parents)
        pstack.extend([p for p in parents[current] if p not in parents])
    astack = [b]    # astack is by construction a topological sort, and therefore a partial order
    while astack:
        current = astack[-1]
        if current in ancestors:
            astack.pop()
            continue
        if all(p in ancestors for p in parents[current]):
            ancestors[current] = set.union(parents[current], *[ancestors[p] for p in parents[current]])
            astack.pop()
        else: # we are missing ancestors
            if current not in visited:
                visited[current] = 1
            else: visited[current] += 1
            astack.extend([p for p in parents[current] if p not in ancestors])
    if any(v > 1 for k,v in visited.items()):
        print(f"ancestors visited multiple times in getallancestors_iterative({int(b)})")
        print(visited)

def cohorts(parents, children=None, initial_cohort=None):
    """ Given the seed of the next cohort (which is the set of beads one step older, in the next
        cohort), build an ancestor/descendant set for each visited bead.  A new cohort is
        formed if we encounter a set of beads, stepping in the descendant direction, for which
        *all* beads in this cohort are ancestors of the first generation of beads in the next
        cohort.
    """
    children     = reverse(parents) if not children else children
    dag          = {"parents": parents, "children": children, "tips": tips(parents, children)}
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
                tail |= dag["children"][b]   # Add the next generation to the tail
            tail |= cohort ^ oldcohort       # Add any beads in oldcohort but not in cohort
            if cohort & dag["tips"]:         # If there are any tips in cohort, add tips to tail
                tail |= dag["tips"]-cohort
            else:
                tail -= cohort               # If there are no tips in cohort subtract off cohort

            oldcohort = copy(cohort)         # Copy so we can tell if new tail has changed anything
                                             # because changing the tail but not cohort may find
                                             # new ancestors

            # Calculate ancestors
            for t in tail:                   # Find all ancestors of all beads in the tail
                if t not in ancestors:
                    # 50.6% of CPU time
                    all_ancestors(t, dag["parents"], ancestors)

            # Calculate cohort
            cohort = set()
            for a in ancestors:
                cohort |= ancestors[a]       # Union all ancestors with the cohort

            # Check termination cases
            if dag["tips"] <= cohort:        # Cohort contains all tips
                head = set()                 # StopIteration and return
                break                        # and yield the current cohort
            if cohort and all(ancestors[t] == cohort for t in tail): # Standard cohort case
                head = copy(tail)            # Head of next cohort is tail from previous iteration
                break                        # Yield successful cohort
            if cohort == oldcohort:          # Cohort hasn't changed, we may be looping
                if dag["tips"] <= tail:      # Tail contains all tips but we didn't form a cohort
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
    """ Find the work in descendants.  Work in ancestors can be found by reverseing the order of
        parents and children:

            ancestor_work = descendant_work(children, parents)
    """
    children        = children if children else reverse(parents)
    bead_work       = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}
    previous_work   = 0
    in_cohorts      = reversed(in_cohorts) if in_cohorts else cohorts(children)
    retval          = {} # The cumulative work for each bead
    for c in in_cohorts:
        sub_children   = sub_braid(c, children)    # children dict within the cohort
        sub_descendants = {}                       # descendants within the cohort
        for b in c:
            all_ancestors(b, sub_children, sub_descendants)
            retval[b] = previous_work + bead_work[b] + sum(bead_work[a] for a in sub_descendants[b])
        # All beads in the next cohort have ALL beads in this cohort as descendants.
        previous_work += sum(bead_work[b] for b in c)
    return retval

def bead_cmp(a, b, work):
    """ A custom cmp(b1,b2) function for sorting beads. This function requires the work function,
        which should be the output of work().

        In the event of a tie it resolves the tie in the following order:
        1. Highest work
        2. FUTURE UNIMPLEMENTED: Lowest hash ("luck")
        3. FUTURE UNIMPLEMENTED: Earliest timestamp
        4. Lowest label (block hash) -- this is "earliest" in simulations

        Use this like:

            work = ancestor_work(parents,children,bead_work)
            cmp = lambda x,y: bead_cmp(x,y,work)
            sort_key = cmp_to_key(lambda x,y: cmp(x,y))

            sorted(beads, key=sort_key)
    """
    if work[a] < work[b]:       # highest work
        return -1
    if work[a] > work[b]:
        return 1
    if a > b:                   # same work, fall back on lexical order
        return -1
    if a < b:
        return 1
    return 0

def work_sort_key(parents, children, bead_work=None, work=None):
    """ Return a sorting key lambda suitable to feed to python's min, max, sort etc. Note that
        sort() sorts values from lowest to highest. When using work_sort_key it will sort beads from
        lowest work to highest. Use `reverse=True` as an argument to sort() if you want the highest
        work, or reverse the resultant list.

        One of <work> or <bead_work> must be passed.

        Use this like:
            work = ancestor_work(parents, children, bead_work)
            sorted(beads, key=max_work_key(parents, work))   # sorted from lowest work to highest
            max(beads, key=work_sort_key(parents, work))     # maximum work
            min(beads, key=work_sort_key(parents, work))     # minimum work
    """
    bead_work = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}
    if bead_work and not work:
        work = work if work else descendant_work(parents,children,bead_work)
    return cmp_to_key(lambda a,b: bead_cmp(a,b,work))

def highest_work_path(parents, children=None, work=None, bead_work=None):
    """ Find the highest (descendant) work path, by following the highest weights through the DAG.

        The highest *ancestor* work path can be found by calling with children and parents reversed:

            highest_work_path(children, parents)
    """
    children  = children if children else reverse(parents)
    bead_work = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}
    work      = work if work else descendant_work(parents, children, bead_work)
    sort_key  = work_sort_key(parents, children, work=work)
    hwpath    = [max(geneses(parents), key=sort_key)]

    while hwpath[-1] not in tips(parents, children):
        hwpath.append(max(generation({hwpath[-1]}, children), key=sort_key))
    return sorted(hwpath)   # return in ascending order no matter whether we're doing ancestor work
                            # or descendant work.

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

def layout(cohort, parents, children=None, bead_work=None):
    """Create a graphical layout of a cohort on a 2D grid with minimal space usage."""

    children  = children if children else reverse(parents)
    bead_work = bead_work if bead_work else {b: FIXED_BEAD_WORK for b in parents}

    # Get the sub-DAG for this cohort. Cast to int to get rid of graph_tool vertices
    sub_parents = dict(sub_braid(cohort, parents).items())
    sub_children = reverse(sub_parents)

    # Get head, tail, and highest work path
    head     = cohort_head(cohort, parents, children)
    tail     = cohort_tail(cohort, parents, children)
    hwpath   = highest_work_path(sub_parents, sub_children)
    width    = len(hwpath)
    work     = descendant_work(parents, children)
    sort_key = work_sort_key(parents, children, work=work)

    # Variables we will fill in
    coords   = bidict() # Bidirectional Map {bead: [x, y]}
    edges    = set()    # {(x,y) for edge crossings}
    unplaced = []      # beads yet to be placed

    # Helper functions
    def place(bead, xy):
        """Mark edge crossings between two beads"""
        nonlocal coords, edges, parents, children
        if bead in coords:
            return coords[bead] == xy # Bead is already in coords at a different locatation
        if xy in coords.inv or xy in edges:
            return False
        newedges = set() # cache new edges in case of success
        for relative in [r for r in [*parents[bead], *children[bead]] if r in coords]:
            x1, y1 = xy
            x2, y2 = coords[relative]
            if x1 > x2:
                x1, x2 = x2, x1
                y1, y2 = y2, y1
            dx = x2 - x1
            dy = y2 - y1
            g = gcd(dx,dy) if dy != 0 else gcd(dx,1)
            step_x = dx // g if dy !=0 else 1
            step_y = dy // g
            for i in range(1, g):
                x = x1 + (step_x*i)
                y = y1 + (step_y*i)
                if (x,y) in coords.inv:
                    return False
                newedges.add((x,y))
        coords[bead] = xy
        edges.update(newedges)
        return True

    def place_unplaced():
        """ Place unplaced beads within the calculated x range. """
        nonlocal coords, unplaced
        for bead in copy(unplaced):
            min_x, max_x = x_range(bead)
            for y in range(1, 15):
                for x in range(min_x, max_x+1):
                    if place(bead, (x,y)):
                        unplaced.remove(bead)
                        break
                if bead in coords:
                    break
        return coords, unplaced

#    def side(edges):
#        """ Return +/- 1 depending on whether the vertex v has a side preference. """
#        sidecnt = 0
#        for e in edges:
#            if pin[e.target()]:
#                sidecnt += int(pos[e.target()][1])
#        return sidecnt//abs(sidecnt) if sidecnt else 0

    def x_range(bead):
        """ Compute minimum and maximum x coordinate for a bead based on parents and children.

            This function is recursive and terminates only if the head and tail have been placed in
            coords.
        """
        nonlocal coords
        def find_xs(bead, parents):
            """ Recurse on parents (or children) until an x coordiate is found, adding <incremenet>
                for each generation traversed. """
            nonlocal coords
            if bead in coords:
                return [coords[bead][0]]
            return [x for p in parents[bead] for x in find_xs(p, parents)]

        #if not find_xs(bead, sub_parents):
        #    print(f"find_xs({bead}, sub_parents) = ", find_xs(bead, sub_parents))
        #    print("sub_parents = ", sub_parents)
        min_x = max(find_xs(bead, sub_parents))
        #if not find_xs(bead, sub_children):
        #    print(f"find_xs({bead}, sub_children) = ", find_xs(bead, sub_children))
        #    print("sub_children = ", sub_children)
        max_x = min(find_xs(bead, sub_children))
        return (min_x+1, max_x-1)

    def insert_x_range():
        """ Attempt to place all unplaced who have x_min > x > x_max by adding columns.
            Return True if columns were inserted.
        """
        nonlocal coords, unplaced
        column_inserted = False
        for bead in unplaced:
            min_x, max_x = x_range(bead)
            if max_x < min_x:
                for insert_x in range(min_x, max_x, -1):
                    insert_row_column(insert_x, 0)
                column_inserted = True
        return column_inserted

    def insert_row_column(x,y):
        """ Insert one row and/or column at x,y. """
        nonlocal coords, edges, width
        edges     = set()           # reset edges and coordinate maps
        oldcoords = copy(coords)
        coords    = bidict()
        for b in oldcoords:
            if b in unplaced:
                continue
            if not place(b, (oldcoords[b][0] if oldcoords[b][0]<x or x==0 else oldcoords[b][0]+1,
                             oldcoords[b][1] if oldcoords[b][1]<y or y==0 else oldcoords[b][1]+1)):
                unplaced.append(b)

    # Main code for layout()

    # Place hwpath beads first
    for x, bead in enumerate(hwpath):
        place(bead, (x,0))

    # Place head beads, excluding those in hwpath
    y = 1
    for bead in sorted(head-set(hwpath), key=sort_key, reverse=True):
        if bead in coords:
            print(f"ERROR: {bead} already has coordinate {coords[bead]}")
        place(bead, (0,y))
        y += 1

    # Place tail beads (excluding those in hwpath)
    y = 1
    if width == 1 and tail != head:
        width = 2 # this happens if there's only one bead in hwpath
    for bead in sorted(tail - head - set(hwpath), key=sort_key, reverse=True):
        if bead in coords:
            print(f"ERROR: {bead} already has coordinate {coords[bead]}")
        place(bead, (width-1, y))
        y += 1

    initial_coords = copy(coords)
    unplaced = sorted(list(cohort - set(coords.keys())), key=lambda b: (x_range(b), -work[b]))
    initial_unplaced = copy(unplaced)

    # Determine if columns need to be inserted because there's not enough space between
    # parents and children based only on head/tail/hwpath.
    if insert_x_range():
        place_unplaced()
    best_coords = copy(coords)
    best_unplaced = copy(unplaced)
    height = max(coords[b][1] for b in coords)+1
    width = max(coords[b][0] for b in coords)+1
    best_area = height * width
    #print(f"Initial graph is {width}x{height} with area {best_area} and unplaced = {unplaced}")

    # Try to optimize area
    while width >= 3:
        coords = copy(initial_coords)
        unplaced = copy(initial_unplaced)
        last_unplaced = copy(best_unplaced)

        # Minimize the area of the resulting graph by inserting rows and columns
        height = max(coords[b][1] for b in coords)+1
        width = max(coords[b][0] for b in coords)+1
        for insert_x in range(width):
            for insert_y in range(height): # FIXME do head and tail separately
                if insert_x == insert_y and insert_x == 0:
                    continue
                coords = copy(initial_coords)
                unplaced = copy(initial_unplaced)
                insert_row_column(insert_x, insert_y)
                place_unplaced()
                while insert_x_range():
                    place_unplaced()
                height = max(coords[b][1] for b in coords)+1
                width = max(coords[b][0] for b in coords)+1
                area = width * height
                if len(unplaced) < len(best_unplaced) or (not unplaced and not best_unplaced and
                                                          area < best_area):
                    best_area = area
                    best_coords = copy(coords)
                    best_unplaced = copy(unplaced)
        if best_unplaced:
            if best_unplaced != last_unplaced:
                print(f"WARNING: continuing because {best_unplaced} are still unplaced.")
                print(f"best_unplaced = {best_unplaced}, last_unplaced = {last_unplaced}")
                continue
            # FIXME this will loop forever if there wasn't an incremental improvement.
            print(f"WARNING: terminating layout() with beads {best_unplaced} still unplaced.")
            for bead in best_unplaced:
                min_x, max_x = x_range(bead)
                print(f"    {bead} should be {min_x} <= x <= {max_x}")
        break

    #print(f"Returning best solution with area {best_area} and unplaced = {best_unplaced}")
    return best_coords

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
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
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
        """ Test an assortment of example *.braid files. """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
            self.assertEqual(list(cohorts(dag["parents"])), dag["cohorts"])

    def test_cohorts_reversed_files(self):
        """ Does it find the same cohorts in the forward and backward directions? """
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
            p = reverse(dag["parents"])
            c = dag["cohorts"]
            c.reverse()
            self.assertEqual(list(cohorts(p)), c, msg="Test file: {filename}")

    def test_highest_work_path(self):
        self.assertEqual(highest_work_path(self.parents1, reverse(self.parents1)), [0,1,2,3])

    def test_higest_work_path_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
            self.assertEqual(highest_work_path(dag["parents"], dag["children"]),
                             dag["highest_work_path"], msg=f"Test file: {filename}")

    def test_check_cohort_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
            for c in dag["cohorts"]:
                self.assertEqual(check_cohort(c, dag["parents"], dag["children"]), True, msg=f"Test file: {filename}")

    def test_check_work_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
            for c in dag["cohorts"]:
                self.assertEqual(dag["work"], work(dag["parents"], dag["children"], dag["bead_work"]),
                                 msg=f"Test file: {filename}")

    def test_sub_braid_files(self):
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
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
        for filename in sorted([filename for filename in os.listdir(TEST_CASE_DIR) if filename.endswith(".braid")]):
            dag = load_braid(filename)
            for c in dag["cohorts"]:
                msg = f"Test file: {filename}"
                self.assertEqual(cohort_head(c, dag["parents"], dag["children"]),
                                 geneses(sub_braid(c, dag["parents"])), msg=msg)
                self.assertEqual(cohort_tail(c, dag["parents"], dag["children"]),
                                 tips(sub_braid(c, dag["parents"])), msg=msg)

if __name__ == "__main__":
    unittest.main()
