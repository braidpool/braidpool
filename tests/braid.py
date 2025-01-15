# A set of tools for manipulating test braids

import json, os, unittest
from copy import copy
from collections import deque, OrderedDict
from functools import cmp_to_key

TEST_CASE_DIR = "braids/"

def make_dag(parents, bead_work=None, description=None):
    """ Make a DAG object which caches the children, geneses, tips, cohorts, and highest work path. """
    dag = {}
    dag["description"]       = description
    dag["parents"]           = parents
    dag["children"]          = reverse(parents)
    dag["geneses"]           = geneses(parents)
    dag["tips"]              = tips(parents, dag["children"])
    dag["cohorts"]           = cohorts(parents)
    dag["bead_work"]         = bead_work if bead_work else {b:1 for b in dag["parents"]}
    dag["work"]              = work(parents, dag["children"], bead_work)
    dag["highest_work_path"] = highest_work_path(parents, dag["children"])
    return dag

def geneses(parents):
    """ Given a dict of {bead: {parents}}, return the set of beads which have no parents. """
    geneses = set()
    for b,p in parents.items():
        if not p: geneses.add(b)
    return geneses

def tips(parents, children=None):
    """ Given a dict of {bead: {parents}}, return the set of beads which have no children. """
    if not children: children = reverse(parents)
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
    """ Given a set of <beads>, compute the set of all children of all {beads}. """
    if not beads: return set()
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
        if p not in ancestors: all_ancestors(p, parents, ancestors)
        ancestors[b].update(ancestors[p])

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
        ancestors = {h: set() for h in head}            # Don't let head have ancestors to stop ancestor iteration
        cohort    = copy(head)                          # Initial cohort is the head

        while True:                                     # DFS search
            # Calculate new tail
            if not head: return                         # StopIteration and return
            else:
                for b in cohort-oldcohort:
                    tail |= dag["children"][b]          # Add the next generation to the tail
                tail |= cohort ^ oldcohort              # Add any beads in the oldcohort but not in the new cohort
                if cohort & dag["tips"]:                # If there are any tips in cohort, add remaining tips to tail:
                    tail |= dag["tips"]-cohort
                else:
                    tail -= cohort                      # If there are no tips in the cohort subtract off the cohort

            oldcohort = copy(cohort)                    # Copy so we can tell that a new tail hasn't changed anything
                                                        # Changing the tail but not cohort may find new ancestors

            # Calculate ancestors
            for t in tail:                              # Find all ancestors of all beads in the tail
                if t not in ancestors:
                    # 50.6% of CPU time
                    all_ancestors(t, dag["parents"], ancestors)

            # Calculate cohort
            cohort = set()
            for a in ancestors: cohort |= ancestors[a]  # Union all ancestors with the cohort

            # Check termination cases
            if dag["tips"] <= cohort:                          # Cohort contains all tips
                head = set()                            # StopIteration and return
                break                                   # and yield the current cohort
            elif cohort and all(ancestors[t] == cohort for t in tail): # Standard cohort case
                head = copy(tail)                       # Head of next cohort is the tail from the previous iteration
                break                                   # Yield successful cohort
            elif cohort == oldcohort:                   # Cohort hasn't changed, we may be looping
                if dag["tips"] <= tail:                        # Tail contains all tips but we didn't form a cohort
                    head = set()                        # We also need cohort == oldcohort (yes)
                    cohort |= tail
                    tail = set()
                    break                               # Yield cohort+tail
                else: cohort.update(tail)               # Seems like I'll be doing 2 loops for non-cohort updates
                                                        # This breaks if I omit the cohort == oldcohort condition.
                                                        #elif not tips & tail and not cohort & tips: (doesn't work)
        oldcohort = set()
        yield cohort

def cohort_tail(cohort, parents, children=None):
    """ Given a cohort as a set of beads, compute its tail. If the tail intersects the tips,
        return all tips.
    """
    children = reverse(parents) if not children else children
    return cohort_head(cohort, parents=children, children=parents)

def cohort_head(cohort, parents, children=None):
    """ Given a cohort as a set of beads, compute its head. If the tail intersects the geneses,
        return all geneses.
    """
    children = reverse(parents) if not children else children
    tail = generation(generation(cohort, parents) - cohort, children)
    tips = geneses(parents)
    if not tail or any({t in tips for t in tail}):
        return tips
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

def work(parents, children=None, bead_work=None):
    """ Find the cumulative work of each bead by adding the work of all ancestor beads.

        <bead_work>: {bead:work} is the self-work for each bead (e.g. 1/x where x is the PoW target)
        With fixed_bead_work=1 per bead, work is equivalent the number of ancestors for each bead.
    """
    if not children: children = reverse(parents)
    fixed_bead_work = 1
    bead_work       = bead_work if bead_work else {b: fixed_bead_work for b in parents}
    previous_work   = 0
    retval          = {} # The cumulative work for each bead
    for c in cohorts(parents):
        sub_parents   = sub_braid(c, parents)    # Parents dict within the cohort
        sub_ancestors = {}                       # Ancestors within the cohort
        head = cohort_head(c, parents, children) # Youngest set of beads in the cohort
        tail = cohort_tail(c, parents, children) # Oldest set of beads in the cohort
        for b in c:
            all_ancestors(b, sub_parents, sub_ancestors)
            retval[b] = previous_work + bead_work[b] + sum([bead_work[a] for a in sub_ancestors[b]])
        # All beads in the next cohort have ALL beads in this cohort as ancestors.
        previous_work += sum([bead_work[b] for b in c])
    return retval

def check_cohort(cohort, parents, children=None):
    """ Check a cohort using check_cohort_ancestors in both directions. """
    children = reverse(parents) if not children else children
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
    children = reverse(parents) if not children else children
    ancestors = dict()
    allancestors = set()
    head = cohort_head(cohort, parents, children)
    for b in cohort:
        all_ancestors(b, parents, ancestors)
        allancestors |= ancestors[b]
    allancestors -= cohort
    if allancestors and generation(allancestors, children) - allancestors != head:
        return False
    return True

def layout(cohort, parents, children, weights=None):
    """Create a left-to-right layout of a cohort on a 2D grid with no edge-bead intersections.
    All coordinates are integers, and edges are considered to intersect beads that lie on
    grid points between the child and parent on the same row.
    """
    children = children if children else reverse(parents)
    cohort_parents  = sub_braid(cohort, parents)
    cohort_children = reverse(cohort_parents)
    bead_work = weights if weights else work(parents, children)
    hwpath = [b for b in highest_work_path(parents, children, weights=weights) if b in cohort]
    coords = {}
    used_coords = set()

    # Initial layout code (unchanged)
    depth_map = {}
    max_depth = 0
    queue = [(b, 0) for b in geneses(cohort_parents)]
    while queue:
        bead, depth = queue.pop(0)
        current_depth = depth_map.get(bead, -1)
        depth_map[bead] = max(current_depth, depth)
        max_depth = max(max_depth, depth_map[bead])
        for child in cohort_children.get(bead, []):
            queue.append((child, depth + 1))

    leaves = set(b for b in cohort_parents if b not in cohort_children or not cohort_children[b])
    for leaf in leaves:
        depth_map[leaf] = max_depth

    beads_by_x = {}
    for bead in cohort_parents:
        x = depth_map[bead]
        beads_by_x.setdefault(x, []).append(bead)

    # Initial placement code (unchanged)
    for x in range(max_depth + 1):
        if x not in beads_by_x:
            continue
        beads = sorted(beads_by_x[x], key=max_work_key(parents,weights), reverse=True)
        bhwpath = [b for b in hwpath if b in beads]
        if len(bhwpath) > 1: print("ERROR: more than one hwpath bead in a column: ", beads)
        elif bhwpath:
            beads.remove(bhwpath[0])
            beads = [bhwpath[0], *beads]

        y = 0
        y_offset = 0

        for bead in beads:
            if y_offset == 0:
                y = 0
            elif y_offset > 0:
                y = y_offset
            else:
                y = y_offset

            while (x, y) in used_coords:
                if y >= 0:
                    y = -(y + 1)
                else:
                    y = -y

            coords[bead] = [x, y]
            used_coords.add((x, y))

            if y >= 0:
                y_offset = y + 1
            else:
                y_offset = -y

    def find_edge_bead_intersections():
        """Find all cases where edges pass through beads on same row."""
        intersections = []

        # Check each child-parent edge
        for child in cohort_parents:
            child_x, child_y = coords[child]
            for parent in cohort_parents[child]:
                parent_x, parent_y = coords[parent]

                # If parent and child are on same row
                if child_y == parent_y:
                    # Check each bead at intermediate x-coordinates on this row
                    for x in range(parent_x + 1, child_x):
                        if (x, child_y) in used_coords:
                            # Find which bead is at this position
                            for b, (bx, by) in coords.items():
                                if bx == x and by == child_y:
                                    intersections.append((b, child, parent))
                                    break

        return intersections

    def move_bead_down(bead, coords, used_coords):
        """Move a bead down to the next available position."""
        x, y = coords[bead]
        new_y = y + 1  # Try one row down

        # Keep moving down until we find a free spot
        while (x, new_y) in used_coords:
            new_y += 1

        used_coords.remove((x, y))
        used_coords.add((x, new_y))
        coords[bead] = [x, new_y]

    # Resolve edge-bead intersections
    while True:
        intersections = find_edge_bead_intersections()
        if not intersections:
            break

        # Move intersected beads down one row at a time
        for bead, _, _ in intersections:
            move_bead_down(bead, coords, used_coords)

    return coords

def oldlayout(cohort, parents, children, weights=None):
    """Create a left-to-right layout of a cohort on a 2D grid.
    Parents are always to the left of their children, leaves are rightmost,
    and beads are placed in rows closest to y=0 based on their work.

    Args:
        parents: Dict mapping beads to their set of parent beads

    Returns:
        Dict mapping beads to their [x,y] coordinates
    """
    children = children if children else reverse(parents)
    cohort_parents  = sub_braid(cohort, parents)
    cohort_children = reverse(cohort_parents)
    bead_work = weights if weights else work(parents, children)
    hwpath = [b for b in highest_work_path(parents, children, weights=weights) if b in cohort]
    coords = {}
    used_coords = set()

    # Compute depth map and identify leaves
    depth_map = {}
    max_depth = 0
    queue = [(b, 0) for b in geneses(cohort_parents)]
    while queue:
        bead, depth = queue.pop(0)
        current_depth = depth_map.get(bead, -1)
        depth_map[bead] = max(current_depth, depth)
        max_depth = max(max_depth, depth_map[bead])
        for child in cohort_children.get(bead, []):
            queue.append((child, depth + 1))

    # Force leaves to rightmost column
    leaves = set(b for b in cohort_parents if b not in cohort_children or not cohort_children[b])
    for leaf in leaves:
        depth_map[leaf] = max_depth

    # Group beads by x-coordinate (depth)
    beads_by_x = {}
    for bead in cohort_parents:
        x = depth_map[bead]
        beads_by_x.setdefault(x, []).append(bead)

    # For each x-coordinate, sort beads by work and assign y-coordinates
    # starting from y=0 and alternating above/below
    for x in range(max_depth + 1):
        if x not in beads_by_x:
            continue

        # Sort beads at this x-coordinate by work (highest to lowest)
        beads = sorted(beads_by_x[x], key=lambda b: bead_work[b], reverse=True)
        print("Considering beads in a column: ", list(map(int, beads)))
        max_work_bead = max_work(beads_by_x[x], parents, bead_work)
        beads.remove(max_work_bead)
        beads = [max_work_bead, *beads]
        print("Sorted column is: ", list(map(int, beads)))
        for b in beads:
            print(f"work[{b}] = {bead_work[b]}, \tlen(parents[{b}]) = {len(parents[b])}")

        y = 0
        y_offset = 0

        for bead in beads:
            if y_offset == 0:
                y = 0
            elif y_offset > 0:
                y = y_offset
            else:
                y = y_offset

            # Find next available y at this x-coordinate
            while (x, y) in used_coords:
                if y >= 0:
                    y = -(y + 1)  # Try below
                else:
                    y = -y  # Try above

            coords[bead] = [x, y]
            used_coords.add((x, y))

            # Update y_offset for next bead
            if y >= 0:
                y_offset = y + 1
            else:
                y_offset = -y

    return coords

def bead_cmp(a, b, parents, weights=None):
    """ A custom cmp(b1,b2) function for sorting beads.

        In the event of a tie it resolves the tie in the following order:
        1. Highest work
        2. FUTURE UNIMPLEMENTED: Lowest hash ("luck")
        3. FUTURE UNIMPLEMENTED: Earliest timestamp
        4. Lowest label (block hash) -- this is "earliest" in simulations

        Use this like:

            sorted(beads, key=cmp_to_key(lambda x,y: braid.bead_cmp(x,y,parents,weights)))
    """
    weights = weights if weights else work(parents)
    if weights[a] < weights[b]: return -1               # highest weight
    elif weights[a] > weights[b]: return 1
    # else both have the same number of parents
    elif a > b: return -1                               # lexical order (lowest first)
    elif a < b: return 1
    else: return 0

def max_work_key(parents, weights=None):
    """ Return a sorting key lambda suitable to feed to python's min, max, sort etc.

        Use this like:
            sorted(beads, key=max_work_key(parents, weights))
    """
    weights = weights if weights else work(parents)
    return cmp_to_key(lambda a,b: bead_cmp(a,b,parents,weights))

def highest_work_path(parents, children=None, weights=None):
    """ Find the highest work path, by following the highest weights through the DAG as given by
        max_work().
    """
    weights = weights if weights else work(parents)
    key     = cmp_to_key(lambda x,y: bead_cmp(x,y,parents,weights))
    hwpath  = [max(tips(parents, children), key=key)]

    while hwpath[-1] not in geneses(parents):
        gen = generation({hwpath[-1]}, parents)
        hwpath.append(max(generation({hwpath[-1]}, parents),
                          key=max_work_key(parents, weights)))
    return list(reversed(hwpath))

def load_braid(filename):
    """ Load a JSON file containing a braid.
    """
    with open(filename) as json_data:
        d = json.load(json_data)
        dag = {}
        dag["description"]       = d["description"]
        dag["parents"]           = {int(k): set(v) for k,v in d["parents"].items()}
        dag["children"]          = {int(k): set(v) for k,v in d["children"].items()}
        dag["geneses"]           = set(d["geneses"])
        dag["tips"]              = set(d["tips"])
        dag["cohorts"]           = [set(map(int,c)) for c in d["cohorts"]]
        if "bead_work" not in d or d["bead_work"] == None:
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
    with open(filename, 'w') as file:
        dag = make_dag(parents)
        result = OrderedDict([
            ("description", description),
            ("parents", {k: list(v) for k,v in dag["parents"].items()}),
            ("children", {k: list(v) for k,v in dag["children"].items()}),
            ("geneses", list(dag["geneses"])),
            ("tips", list(dag["tips"])),
            ("cohorts", [sorted(list(map(int, c))) for c in dag["cohorts"]]),
            ("bead_work", dag["bead_work"]),
            ("work", dag["work"]),
            ("highest_work_path", dag["highest_work_path"])
        ])
        file.write(json.dumps(result, sort_keys=False, indent=4))
        file.close()

class TestCohortMethods(unittest.TestCase):
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
