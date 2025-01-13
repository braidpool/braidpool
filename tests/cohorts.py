# A set of tools for manipulating test braids

import json, os, unittest
from copy import copy
from collections import deque, OrderedDict

def makedag(parents, description=None):
    """ Make a DAG object which caches the children, geneses, tips, cohorts, and highest work path. """
    dag = {}
    dag["description"] = description
    dag["parents"] = parents
    dag["children"] = reverse(parents)
    dag["cohorts"] = cohorts(parents)
    dag["geneses"] = geneses(parents)
    dag["tips"] = geneses(dag["children"])
    dag["highestworkpath"] = highest_work_path(parents, dag["children"])
    return dag

def geneses(parents):
    """ Given a dict of {bead: {parents}}, return the set of beads which have no parents. """
    geneses = set()
    for b,p in parents.items():
        if not p: geneses.add(b)
    return geneses

def tips(parents):
    """ Given a dict of {bead: {parents}}, return the set of beads which have no children. """
    return geneses(reverse(parents))

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

def generation(beads, children):
    """ Given a set of <beads>, compute the set of all children of all {beads}. """
    if not beads: return set()
    retval = set()
    for b in beads:
        retval |= children[b]
    return retval

def getallancestors(b, parents, ancestors):
    """ Gets all ancestors for a bead <b>, filling in ancestors of
        any other ancestors encountered, using a recursive
        algorithm.  Assumes b not in parents and b not in ancestors.
    """
    ancestors[b] = set(copy(parents[b]))
    for p in parents[b]:
        if p not in ancestors: getallancestors(p, parents, ancestors)
        ancestors[b].update(ancestors[p])

def cohorts(parents, initial_cohort=None):
    """ Given the seed of the next cohort (which is the set of beads one step older, in the next
        cohort), build an ancestor/descendant set for each visited bead.  A new cohort is
        formed if we encounter a set of beads, stepping in the descendant direction, for which
        *all* beads in this cohort are ancestors of the first generation of beads in the next
        cohort.
    """
    dag          = {"parents": parents, "children": reverse(parents), "tips": tips(parents)}
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
                    getallancestors(t, dag["parents"], ancestors)

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

def cohort_head(cohort, parents, children):
    """ Given a cohort as a set of beads, compute its head. """
    return cohort_headtail(cohort, parents, children)

def cohort_tail(cohort, parents, children):
    """ Given a cohort as a set of beads, compute its tail. If the tail intersects the tips, return all tips. """
    return cohort_headtail(cohort, children, parents)

def cohort_headtail(cohort, parents, children):
    tail = generation(generation(cohort, parents) - cohort, children)
    tips = geneses(parents)
    if not tail or any({t in tips for t in tail}):
        return tips
    return tail

def highest_work_path(parents, children):
    """ Find the highest work path by adding the work of each parent
        bead using BFS.  We only need to do this within cohorts, since a
        cohort has all the same ancestors and descendants. This assumes
        all beads have the same work.
    """
    hwpath = []
    work = 1 # work per bead. Update this if if a DAA is used and different beads have different work
    for c in cohorts(parents):
        head = cohort_head(c, parents, children) # Youngest set of beads in the cohort
        tail = cohort_tail(c, parents, children) # Oldest set of beads in the cohort
        if head == tail:
            hwpath.append(next(iter(c)))
            continue
        queue = deque(set.union(*[children[h] for h in head]))
        weights = {h: work for h in head}

        # build weights dict
        while queue:
           b = queue.pop()
           cparents = generation({b}, parents)
           if b not in weights:
               missingparents = [p for p in cparents if p not in weights]
               if missingparents:
                   queue.extend(missingparents)
                   continue
               else:
                   weights[b] = work + sum([weights[p] for p in cparents])
                   queue.extendleft(generation({b}, children))

        # Follow the highest weights through the DAG from tail to head and build hwpath
        chwpath = [max(tail, key=lambda x: weights[x])]
        while chwpath[-1] not in head:
            chwpath.append(max(generation({chwpath[-1]}, parents), key=lambda x: weights[x]))
        hwpath.extend(reversed(chwpath))
    return hwpath

def load_braid(filename):
    """ Load a JSON file containing a braid.
    """
    with open(filename) as json_data:
        d = json.load(json_data)
        dag = {}
        dag["description"] = d["description"]
        dag["parents"] = {int(k): set(v) for k,v in d["parents"].items()}
        dag["children"] = {int(k): set(v) for k,v in d["children"].items()}
        dag["cohorts"] = [set(map(int,c)) for c in d["cohorts"]]
        dag["highestworkpath"] = d["highestworkpath"]
        dag["tips"] = set(d["tips"])
        dag["geneses"] = set(d["geneses"])

        json_data.close()
        return dag

def save_braid(parents, filename, description=None):
    """ Save a JSON file containing a braid. It should contain the keys "description", "parents",
        "cohorts", and "workpath"
    """
    with open(filename, 'w') as file:
        dag = makedag(parents)
        result = OrderedDict([
            ("description", description),
            ("parents", {k: list(v) for k,v in dag["parents"].items()}),
            ("children", {k: list(v) for k,v in dag["children"].items()}),
            ("geneses", list(dag["geneses"])),
            ("tips", list(dag["tips"])),
            ("cohorts", [sorted(list(map(int, c))) for c in dag["cohorts"]]),
            ("highestworkpath", dag["highestworkpath"])
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
        for filename in sorted([filename for filename in os.listdir() if filename.endswith(".braid")]):
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
        for filename in sorted([filename for filename in os.listdir() if filename.endswith(".braid")]):
            dag = load_braid(filename)
            self.assertEqual(list(cohorts(dag["parents"])), dag["cohorts"])

    def test_cohorts_reversed_files(self):
        """ Does it find the same cohorts in the forward and backward directions? """
        for filename in sorted([filename for filename in os.listdir() if filename.endswith(".braid")]):
            dag = load_braid(filename)
            p = reverse(dag["parents"])
            c = dag["cohorts"]
            c.reverse()
            self.assertEqual(list(cohorts(p)), c)

    def test_highest_work_path(self):
        self.assertEqual(highest_work_path(self.parents1, reverse(self.parents1)), [0,1,2,3])

    def test_higest_work_path_files(self):
        for filename in sorted([filename for filename in os.listdir() if filename.endswith(".braid")]):
            dag = load_braid(filename)
            self.assertEqual(highest_work_path(dag["parents"], dag["children"]), dag["highestworkpath"])


if __name__ == "__main__":
    unittest.main()
