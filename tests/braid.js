/**
 * A set of tools for manipulating test braids. The algorithms herein are intended to work with any
 * bead object supporting comparison (for lexical ordering when PoW ordering fails) and conversion to a number
 * (for dumping to a file).
 * Since parents are always explicitly passed in, we don't depend on getting parents from the Bead
 * object used.
 */

const fs = require('fs');
const path = require('path');

const TEST_CASE_DIR = "braids/";
const FIXED_BEAD_WORK = 1; // The work per bead if work is not passed.

// Helper BiMap implementation (replaces Python's bidict)
class BiMap {
    constructor() {
        this._map = new Map();
        this._inverse = new Map();
    }

    set(key, value) {
        if (this._map.has(key)) {
            this._inverse.delete(this._map.get(key));
        }
        if (this._inverse.has(value)) {
            this._map.delete(this._inverse.get(value));
        }
        this._map.set(key, value);
        this._inverse.set(value, key);
    }

    get(key) {
        return this._map.get(key);
    }

    getKey(value) {
        return this._inverse.get(value);
    }

    has(key) {
        return this._map.has(key);
    }

    hasValue(value) {
        return this._inverse.has(value);
    }

    delete(key) {
        if (this._map.has(key)) {
            const value = this._map.get(key);
            this._map.delete(key);
            this._inverse.delete(value);
            return true;
        }
        return false;
    }

    deleteValue(value) {
         if (this._inverse.has(value)) {
            const key = this._inverse.get(value);
            this._map.delete(key);
            this._inverse.delete(value);
            return true;
        }
        return false;
    }

    get size() {
        return this._map.size;
    }

    * [Symbol.iterator]() {
        yield* this._map.entries();
    }

    entries() {
        return this._map.entries();
    }

    keys() {
        return this._map.keys();
    }

    values() {
        return this._map.values();
    }

    get inverse() {
        // Create a proxy or a new BiMap if modification is needed,
        // for now, just provide access to the internal inverse map for lookup.
        // A more robust implementation might return a new BiMap or a read-only view.
        const inv = new BiMap();
        inv._map = this._inverse;
        inv._inverse = this._map;
        return inv;
    }
}


/**
 * Make a DAG object which caches the children, geneses, tips, cohorts,
 * and highest work path.
 * @param {Map<any, Set<any>>} hashedParents - Map of {beadHash: Set<parentHashes>}
 * @param {Map<number, number>} [beadWork] - Optional map of {beadId: work}
 * @param {string} [description] - Optional description.
 * @returns {object} DAG object.
 */
function makeDag(hashedParents, beadWork = null, description = null) {
    const parents = numberBeads(hashedParents); // Map<number, Set<number>>
    const dag = {};
    dag.description = description;
    dag.parents = parents; // Map<number, Set<number>>
    dag.children = reverse(parents); // Map<number, Set<number>>
    dag.geneses = geneses(parents); // Set<number>
    dag.tips = tips(parents, dag.children); // Set<number>
    dag.cohorts = Array.from(cohorts(parents, dag.children)); // Array<Set<number>>
    dag.beadWork = beadWork ? new Map(beadWork) : new Map([...parents.keys()].map(b => [b, FIXED_BEAD_WORK])); // Map<number, number>
    dag.work = descendantWork(parents, dag.children, dag.beadWork, dag.cohorts); // Map<number, number>
    dag.highestWorkPath = highestWorkPath(parents, dag.children, dag.beadWork, dag.work); // Array<number>
    return dag;
}

/**
 * Given a map of {bead: Set<parents>}, return the set of beads which have no parents.
 * @param {Map<number, Set<number>>} parents - Map of {beadId: Set<parentId>}
 * @returns {Set<number>} Set of genesis bead IDs.
 */
function geneses(parents) {
    const retval = new Set();
    for (const [b, p] of parents.entries()) {
        if (!p || p.size === 0) { // Check if p exists and is empty
            retval.add(b);
        }
    }
    return retval;
}

/**
 * Given a map of {bead: Set<parents>}, return the set of beads which have no children.
 * @param {Map<number, Set<number>>} parents - Map of {beadId: Set<parentId>}
 * @param {Map<number, Set<number>>} [children] - Optional precomputed children map.
 * @returns {Set<number>} Set of tip bead IDs.
 */
function tips(parents, children = null) {
    children = children ? children : reverse(parents);
    return geneses(children); // Tips of the original graph are geneses of the reversed graph
}

/**
 * Given a map of {bead: Set<parents>}, compute the corresponding {bead: Set<children>} (or vice-versa).
 * @param {Map<number, Set<number>>} parentsOrChildren - Map of {beadId: Set<parentId>} or {beadId: Set<childId>}
 * @returns {Map<number, Set<number>>} Reversed map.
 */
function reverse(parentsOrChildren) {
    const reversed = new Map();
    // Ensure all beads mentioned anywhere exist as keys in the reversed map
    const allBeads = new Set(parentsOrChildren.keys());
     for (const relatedSet of parentsOrChildren.values()) {
         for (const related of relatedSet) {
             allBeads.add(related);
         }
     }
     for (const bead of allBeads) {
        if (!reversed.has(bead)) {
            reversed.set(bead, new Set());
        }
    }


    for (const [bead, relatedSet] of parentsOrChildren.entries()) {
        for (const related of relatedSet) {
            // 'related' should already exist as a key from the pre-population step
            reversed.get(related).add(bead);
        }
    }
    return reversed;
}

/**
 * Given a set of <beads>, compute the set of all children (or parents) of all beads in the set.
 * @param {Set<number>} beads - Set of bead IDs.
 * @param {Map<number, Set<number>>} relationMap - Map representing children or parents {beadId: Set<relatedId>}.
 * @returns {Set<number>} Set of related bead IDs.
 */
function generation(beads, relationMap) {
    const retval = new Set();
    for (const b of beads) {
        const relatedNodes = relationMap.get(b); // Get the Set of related nodes
        if (relatedNodes) { // Check if the bead exists in the map and has related nodes
            for (const related of relatedNodes) {
                retval.add(related);
            }
        }
    }
    return retval;
}

/**
 * Gets all ancestors for a bead <b>, filling in ancestors of any other
 * ancestors encountered, using an iterative algorithm.
 * @param {number} b - The bead ID to start from.
 * @param {Map<number, Set<number>>} parents - The parent map {beadId: Set<parentId>}.
 * @param {Map<number, Set<number>>} [ancestors=new Map()] - Cache for ancestor sets. Modified in place.
 * @returns {Map<number, Set<number>>} The updated ancestors cache.
 */
function allAncestors(b, parents, ancestors = new Map()) {
    const workStack = []; // [bead, is_processed]

    // Initial population of stack for bead 'b' if not already processed
    if (!ancestors.has(b)) {
        workStack.push([b, false]);
    }

    while (workStack.length > 0) {
        const lastIndex = workStack.length - 1;
        let [current, isProcessed] = workStack[lastIndex]; // Use let for modification

        // If bead somehow not in parents map (e.g., disconnected graph part), treat as genesis.
        const currentParents = parents.get(current);
        if (currentParents === undefined) {
             // console.warn(`Bead ${current} not found in parents map during allAncestors. Treating as genesis.`);
             if (!ancestors.has(current)) {
                 ancestors.set(current, new Set()); // Ensure it exists with no ancestors
             }
             workStack.pop(); // Remove from stack
             continue; // Process next item
        }


        if (isProcessed) {
            // We've finished processing all parents, compute ancestors for 'current'
            workStack.pop(); // Remove the processed item

            const calculatedAncestors = new Set(currentParents); // Start with direct parents

            // Update with ancestors of all *direct* parents
            for (const p of currentParents) {
                // Parent 'p' must be in ancestors map because we processed it earlier (due to stack logic)
                const parentAncestors = ancestors.get(p);
                if (parentAncestors) { // Check if parent's ancestors are calculated
                    for (const ancestorP of parentAncestors) {
                        calculatedAncestors.add(ancestorP);
                    }
                } else {
                    // This indicates a logic error in the stack processing if a parent isn't found
                     console.error(`Consistency error: Ancestor info for parent ${p} of bead ${current} not found.`);
                     // Handle potential error: maybe treat parent 'p' as having no ancestors?
                }
            }
            ancestors.set(current, calculatedAncestors); // Store computed ancestors

        } else {
            // Mark 'current' as being processed now
            workStack[lastIndex][1] = true; // Modify in place: [current, true]

            // Add any *unprocessed* parents to the stack
            let addedParentToStack = false;
            for (const p of currentParents) {
                if (!ancestors.has(p)) {
                     // Check if already in stack to prevent redundant processing
                     const stackIndex = workStack.findIndex(item => item[0] === p);
                     if (stackIndex === -1) { // Not in stack yet
                          workStack.push([p, false]); // Add parent to be processed
                          addedParentToStack = true;
                     }
                }
            }
        }
    } // End while loop

    // Final check: Ensure the starting bead 'b' itself has an entry in the ancestors map,
    if (!ancestors.has(b)) {
         const bParents = parents.get(b) || new Set();
         const calculatedAncestors = new Set(bParents);
          for (const p of bParents) {
                const parentAncestors = ancestors.get(p);
                if (parentAncestors) {
                    for (const ancestorP of parentAncestors) {
                        calculatedAncestors.add(ancestorP);
                    }
                }
           }
         ancestors.set(b, calculatedAncestors);
    }


    return ancestors;
}


/**
 * Generates cohorts of a Braid.
 * @param {Map<number, Set<number>>} parents - The parent map {beadId: Set<parentId>}.
 * @param {Map<number, Set<number>>} [children] - Optional precomputed children map.
 * @param {Set<number>} [initialCohort] - Optional starting cohort (defaults to geneses).
 * @yields {Set<number>} The next cohort in the DAG.
 */
function* cohorts(parents, children = null, initialCohort = null) {
    // How in the holy fuck does js not have a set equality operator?!?!
    isEqual = (setA, setB) => setA.size === setB.size && setA.isSubsetOf(setB);

    children = children ? children : reverse(parents);
    const dag_tips = tips(parents, children);
    let cohort = initialCohort ? initialCohort : geneses(parents);
    let oldcohort = new Set();
    let head = new Set(cohort);
    let tail = new Set(cohort);
    while (true) {
        const ancestors = new Map();
        for (const h of head) { ancestors.set(h, new Set()); }
        cohort = new Set(head);

        while (true) {
            if (head.size === 0) { return; }
            for (const b of cohort.difference(oldcohort)) {
                 tail = tail.union(children.get(b));
            }
            tail = tail.union(cohort.symmetricDifference(oldcohort));
            if (cohort.intersection(dag_tips).size > 0) {
                tail = tail.union(dag_tips.difference(cohort));
            } else {
                tail = tail.difference(cohort);
            }

            oldcohort = new Set(cohort);

            // Calculate ancestors
            for (const t of tail.difference(new Set(ancestors.keys()))) {
                allAncestors(t, parents, ancestors); // Modifies 'ancestors' Map
            }

            // Compute new cohort
            cohort = new Set();
            for(const v of ancestors.values()) {
                cohort = cohort.union(v);
            }

            // Check termination cases
            if (dag_tips.isSubsetOf(cohort)) {
                head = new Set();
                break;
            }

            let standardCohortCondition = true;
            for (const t of tail) {
                if (!cohort.size || !isEqual(ancestors.get(t), cohort)) {
                    standardCohortCondition = false;
                    break;
                }
            }
            if (standardCohortCondition) {
                head = new Set(tail);
                break;
            }

            if (isEqual(cohort, oldcohort)) {
                if (dag_tips.isSubsetOf(tail)) {
                    head = new Set();
                    cohort = cohort.union(tail);
                    tail = new Set();
                    break;
                }
                cohort = cohort.union(tail);
            } // End Inner Loop Body
        } // End inner while loop

        oldcohort = new Set();
        yield cohort;

    }
}


/**
 * Given a cohort as a set of beads, compute its tail.
 * @param {Set<number>} cohort - The cohort set.
 * @param {Map<number, Set<number>>} parents - The parent map.
 * @param {Map<number, Set<number>>} [children] - Optional children map.
 * @returns {Set<number>} The tail of the cohort.
 */
function cohortTail(cohort, parents, children = null) {
    children = children ? children : reverse(parents);
    // Tail is the "head" of the reversed graph
    return cohortHead(cohort, children, parents);
}


/**
 * Given a cohort as a set of beads, compute its head.
 * Matches the logic of the Python implementation.
 * @param {Set<number>} cohort - The cohort set.
 * @param {Map<number, Set<number>>} parents - The parent map for the entire DAG.
 * @param {Map<number, Set<number>>} [children] - Optional children map for the entire DAG.
 * @returns {Set<number>} The head of the cohort.
 */
function cohortHead(cohort, parents, children = null) {
    children = children ? children : reverse(parents); // Ensure children map exists
    const dagGeneses = geneses(parents); // Get DAG geneses (Python's 'cohort_tips')

    // Calculate head candidate (Python's 'tail' variable logic)
    const cohortParents = generation(cohort, parents); // Step 1: Parents of cohort members
    const externalParents = new Set([...cohortParents].filter(p => !cohort.has(p))); // Step 2: Parents outside cohort
    const headCandidate = generation(externalParents, children); // Step 3: Children of external parents

    // Check termination condition (Python lines 192-193)
    let intersectsGeneses = false;
    if (headCandidate.size > 0) { // Only check intersection if headCandidate is not empty
        for (const h of headCandidate) {
            if (dagGeneses.has(h)) {
                intersectsGeneses = true;
                break;
            }
        }
    }

    // Return based on termination condition
    if (headCandidate.size === 0 || intersectsGeneses) {
        // Python returns *all* DAG geneses in this case
        return dagGeneses;
    } else {
        // Otherwise, return the calculated head candidate
        return headCandidate;
    }
}


/**
 * Given a set of <beads>, return the sub-DAG corresponding to only those beads.
 * @param {Set<number>} beads - The set of bead IDs for the sub-graph.
 * @param {Map<number, Set<number>>} parents - The parent map for the full DAG.
 * @returns {Map<number, Set<number>>} The parent map for the sub-DAG.
 */
function subBraid(beads, parents) {
    const subParents = new Map();
    for (const b of beads) {
        // Ensure every bead in the set exists as a key in the sub-braid
        subParents.set(b, new Set());
        if (parents.has(b)) {
            const beadParents = parents.get(b);
            for (const p of beadParents) {
                if (beads.has(p)) { // Only include parents that are also in the bead set
                    subParents.get(b).add(p);
                }
            }
        }
    }
    return subParents;
}


/**
 * Find the work in descendants.
 * Work in ancestors can be found by reversing the order of parents and children.
 * @param {Map<number, Set<number>>} parents - The parent map for the entire DAG.
 * @param {Map<number, Set<number>>} [children] - Optional precomputed children map.
 * @param {Map<number, number>} [beadWork] - Optional map of work per bead.
 * @param {Array<Set<number>>} [inCohorts] - Optional precomputed cohorts array (ordered geneses to tips).
 * @returns {Map<number, number>} Map of {beadId: cumulativeDescendantWork}.
 */
function descendantWork(parents, children = null, beadWork = null, inCohorts = null) {
    if (!parents) return new Map(); // Handle null/undefined input
    children = children ? children : reverse(parents);
    if(!beadWork) {
        beadWork = new Map([...allBeads].map(b => [b, FIXED_BEAD_WORK]));
    }
    let previousWork = 0;
    let revCohorts;
    if (inCohorts) {
        revCohorts = [...inCohorts].reverse();
    } else {
        revCohorts = Array.from(cohorts(children, parents));
    }
    const returnValue = new Map();

    for (const c of revCohorts) {
        const subChildren = subBraid(c, children);
        const subDescendants = new Map();
        for (const b of c) {
            allAncestors(b, subChildren, subDescendants);
            let sumOfSubDescendantWork = 0;
            for (const a of subDescendants.get(b)) {
                sumOfSubDescendantWork += beadWork.get(a);
            }
            returnValue.set(b, previousWork + beadWork.get(b) + sumOfSubDescendantWork);
        }
        for (const b of c) {
            previousWork += beadWork.get(b);
        }
    }
    return returnValue;
}


/**
 * Comparison function for sorting beads based on work.
 * @param {number} a - First bead ID.
 * @param {number} b - Second bead ID.
 * @param {Map<number, number>} dWork - Descendant work map.
 * @param {Map<number, number>} [aWork] - Optional ancestor work map.
 * @returns {number} -1 if a < b, 1 if a > b, 0 if equal. Sorts highest work first.
 */
function beadCompare(a, b, dWork, aWork = null) {
    const workA = dWork.get(a) || 0;
    const workB = dWork.get(b) || 0;

    // 1. Highest descendant work first
    if (workA > workB) return -1;
    if (workA < workB) return 1;

    // 2. Highest ancestor work first (if available)
    if (aWork) {
        const ancWorkA = aWork.get(a) || 0;
        const ancWorkB = aWork.get(b) || 0;
        if (ancWorkA > ancWorkB) return -1;
        if (ancWorkA < ancWorkB) return 1;
    }

    // 3. Lowest bead ID first (tie-breaker, simulates hash comparison)
    if (a < b) return -1;
    if (a > b) return 1;

    return 0; // Beads are identical or have same work/ID
}

/**
 * Returns a comparison function suitable for Array.prototype.sort().
 * @param {Map<number, Set<number>>} parents - Parent map.
 * @param {Map<number, Set<number>>} [children] - Optional children map.
 * @param {Map<number, number>} [beadWork] - Work per bead map.
 * @returns {function(number, number): number} Comparison function.
 */
function workSortComparator(parents, children = null, beadWork = null) {
    children = children ? children : reverse(parents);
    beadWork = beadWork ? beadWork : new Map([...parents.keys()].map(b => [b, FIXED_BEAD_WORK]));
    const dWork = descendantWork(parents, children, beadWork);
    const aWork = descendantWork(children, parents, beadWork); // Ancestor work

    // Note: JS sort expects negative if a < b. Our beadCompare returns -1 if a > b (higher work first).
    // So, we use beadCompare directly.
    return (a, b) => beadCompare(a, b, dWork, aWork);
}

/**
 * Find the highest (descendant) work path through the DAG.
 * @param {Map<number, Set<number>>} parents - Parent map.
 * @param {Map<number, Set<number>>} [children] - Optional children map.
 * @param {Map<number, number>} [beadWork] - Work per bead map.
 * @param {Map<number, number>} [dWork] - Optional precomputed descendant work map.
 * @returns {Array<number>} Array of bead IDs in the highest work path.
 */
function highestWorkPath(parents, children = null, beadWork = null, dWork = null) {
    children = children ? children : reverse(parents);
    beadWork = beadWork ? beadWork : new Map([...parents.keys()].map(b => [b, FIXED_BEAD_WORK]));
    const comparator = workSortComparator(parents, children, beadWork); // Gets the comparison function
    const dagGeneses = geneses(parents);
    const dagTips = tips(parents, children);

    if (dagGeneses.size === 0) return []; // Empty graph

    // Find the genesis bead with the highest work according to the comparator
    const sortedGeneses = [...dagGeneses].sort(comparator);
    if (sortedGeneses.length === 0) return []; // No valid geneses
    const startBead = sortedGeneses[0]; // Highest work is first element after sort

    const hwPath = [startBead];

    while (!dagTips.has(hwPath[hwPath.length - 1])) {
        const currentBead = hwPath[hwPath.length - 1];
        const currentChildren = children.get(currentBead) || new Set();

        if (currentChildren.size === 0) {
            // Should have been caught by dagTips check if currentBead is a tip.
            if (!dagTips.has(currentBead)) {
                 console.warn(`Highest work path reached bead ${currentBead} which is not a tip but has no children.`);
            }
            break; // Stop path extension
        }

        // Find the child with the highest work according to the comparator
        const sortedChildren = [...currentChildren].sort(comparator);
         if (sortedChildren.length === 0) {
              // Should not happen if currentChildren.size > 0
              console.warn(`Highest work path: Bead ${currentBead} has children set, but sorted result is empty.`);
              break;
         }
        const nextBead = sortedChildren[0]; // Highest work child is first
        hwPath.push(nextBead);

        // Safety break for potential cycles or errors in large graphs
        if (hwPath.length > parents.size * 2) { // Heuristic limit
             console.error("Highest work path calculation exceeded graph size * 2. Stopping to prevent potential infinite loop.");
             break;
        }
    }
    return hwPath;
}

// --- Layout Function ---

/**
 * Places beads on a grid based on DAG structure and highest work path for a single cohort.
 * @param {Set<number>} cohort - Set of beads in the cohort.
 * @param {Map<number, Set<number>>} allParents - Parent map for the entire DAG.
 * @param {Map<number, number>} [beadWork] - Optional work map for the entire DAG.
 * @param {Map<number, [number, number]>} [previousCohortTipsPos] - Optional map of {tipId: [x, y]} from the previous cohort's layout result (tipsPos).
 * @returns {[Map<number, [number, number]>, Map<number, [number, number]>]} [posMap, tipsPosMap] Map of bead to [x, y] coordinates, and Map of cohort tips to [x,y] coordinates.
 */
function layout(cohort, allParents, beadWork = null, previousCohortTipsPos = null) {
    function intersection(x1, y1, x2, y2, x3, y3) {
        // Check if the point (x3, y3) lies on the line segment from (x1, y1) to (x2, y2)
        // Ignore duplicate endpoints
        if ((x1 === x3 && y1 === y3) || (x2 === x3 && y2 === y3)) {
            return false;
        }
        // Check for collinearity using cross-product (or checking slopes)
        const crossProduct = (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1);
        // Use a small tolerance for floating point comparison if necessary, though integer coords assumed here
        if (Math.abs(crossProduct) > 1e-9) { // Javascript can't do integer math
            return false;
        }
        // Check if point lies within the bounding box of the segment
        const withinX = Math.min(x1, x2) <= x3 && x3 <= Math.max(x1, x2);
        const withinY = Math.min(y1, y2) <= y3 && y3 <= Math.max(y1, y2);
        return withinX && withinY;
    }

    // setXCoord sets the values in proposedX
    const proposedX = new Map();

    function setXCoord(bead, localParents, localChildren, localHead) {
        // Set an x-coordinate for a bead based on being right of its parents
        // and left of its children.
        if (proposedX.has(bead)) {
            return;
        }

        // Determine the minimum x-coordinate based on parents
        let minX = 0;
        if (localHead.has(bead)) {
            minX = 0; // Beads in the head start at 0 if no other constraints
        } else {
            const beadParents = localParents.get(bead) || new Set();
            for (const parent of beadParents) {
                // Recursive call ensures parents are processed first
                setXCoord(parent, localParents, localChildren, localHead);
                minX = Math.max(minX, proposedX.get(parent) + 1);
            }
        }

        // Determine the maximum x-coordinate based on children (soft constraint)
        let maxX = Infinity;
        const beadChildren = localChildren.get(bead) || new Set();
        for (const child of beadChildren) {
            if (proposedX.has(child)) {
                maxX = Math.min(maxX, proposedX.get(child) - 1);
            }
        }

        // Handle constraint conflict: if min_x > max_x, shift children
        if (minX > maxX && maxX < Infinity) {
            const beadChildren = localChildren.get(bead) || new Set();
            for (const child of beadChildren) {
                if (proposedX.get(child) !== undefined && proposedX.get(child) <= minX) {
                    const shiftAmount = minX + 1 - proposedX.get(child);
                    for (const other of proposedX.keys()) {
                        if (proposedX.get(other) >= proposedX.get(child)) {
                            proposedX.set(other, proposedX.get(other) + shiftAmount);
                        }
                    }
                }
            }
        }
        // Set the final X for the current bead after resolving conflicts
        proposedX.set(bead, minX);
    }

    const allChildren = reverse(allParents);
    // Connectivity from previous tips (Map<number, Set<number>>)
    // Get children of the previous tip that are in the current cohort
    const previousCohortEdges = new Map();
    if (previousCohortTipsPos) {
        for (const tipId of previousCohortTipsPos.keys()) {
            previousCohortEdges.set(tipId, allChildren.get(tipId));
        }
    }
    const parents = subBraid(cohort, allParents); // Parents within the cohort
    const children = reverse(parents);          // Children within the cohort
    // Ensure beadWork covers all necessary beads, defaulting if needed
    const cohortBeadWork = new Map();
    const allRelevantBeads = new Set([...cohort, ...(previousCohortTipsPos ? previousCohortTipsPos.keys() : [])]);
    for (const bead of allRelevantBeads) {
        let work = beadWork?.get(bead);
        if (work === undefined || work === null) {
             // If beadWork provided but missing entry, or beadWork null, use default
             if (allParents.has(bead) || cohort.has(bead)) { // Check if it's a valid bead in the context
                  work = FIXED_BEAD_WORK;
             } else {
                  // If it's a tip from previous and not in allParents (e.g., genesis of prev graph), default work?
                  // Python version seems to assume bead_work covers all parents. Let's default to 0 or 1 for safety.
                  work = FIXED_BEAD_WORK; // Defaulting to 1 for consistency
             }
        }
        cohortBeadWork.set(bead, work);
    }

    // Calculate HWP using only work values for beads *within* the current cohort
    const hwPath = highestWorkPath(parents, children, cohortBeadWork);
    const head = cohortHead(cohort, parents, children);
    const tail = cohortTail(cohort, parents, children);

    // Assign x-coordinates to hwpath beads in order of decreasing work along the y=0 axis
    hwPath.forEach((bead, i) => proposedX.set(bead, i));

    // Try to assign x coordinates to all beads based on being right of their parents and left of their children
    for (const bead of new Set([...cohort].filter(b => !hwPath.includes(b)))) {
        setXCoord(bead, parents, children, head);
    }

    // Find the maximum x-coordinate
    let maxX = Math.max(...proposedX.values());

    // Put beads with no children to be at the right edge
    for (const bead of tail.difference(new Set(hwPath))) {
         proposedX.set(bead, maxX);
    }

    // Ensure consistency for hwpath which may have moved due to parent-child relationships.
    for (let i = 0; i < hwPath.length - 1; i++) {
        if (proposedX.get(hwPath[i]) >= proposedX.get(hwPath[i+1])) {
            proposedX.set(hwPath[i+1], proposedX.get(hwPath[i]) + 1);
        }
    }

    const pos = new Map(); // { beadId: [x, y] }
    hwPath.forEach(bead => pos.set(bead, [proposedX.get(bead), 0]));

    // A running tally of lines on the graph
    const lines = []; // Array of { p: [x, y], c: [x, y] } coordinate pairs for existing lines

    const extendedChildren = new Map(children); // Includes children within cohort and to cohort from prev tips
    for(const [p, cSet] of previousCohortEdges.entries()) {
        if (!children.has(p)) {
            extendedChildren.set(p, new Set());
        }
        extendedChildren.set(p, cSet.union(extendedChildren.get(p)));
    }
    const extendedParents = reverse(extendedChildren);
    if (previousCohortTipsPos) {
        for (const [tipId, tipPos] of previousCohortTipsPos.entries()) {
            pos.set(tipId, [-1, tipPos[1]]); // Add previous tip position
        }
    }

    // Place remaining beads in work sorted order (lowest work at top)
    const remainingY = [...cohort].filter(b => !hwPath.includes(b));
    // Sort remaining beads by highest work
    const comparator = workSortComparator(parents, children, cohortBeadWork);
    remainingY.sort((a, b) => comparator(a, b)); // Sorts highest work first

    for (const bead of remainingY) {
        const x = proposedX.get(bead);
        let dist = 0;
        let placed = false;
        let y = 0;

        while (true) {
            dist++;
            if (y <= 0) {
                y += dist;
            } else {
                y -= dist;
            }

            // if [x,y] in pos.values(): continue
            let occupied = false;
            for (const [x1,y1] of pos.values()) {
                if (x1 === x && y1 === y) {
                    occupied = true;
                    break;
                }
            }
            if (occupied) continue;

            // Create a list of all lines on the graph including the proposed <bead> position [x,y]
            pos.set(bead, [x, y]); // Temporarily place the bead
            const newLines = []; // {p: [x,y], c: [x,y]}
            const beadPos = pos.get(bead);
            for (const p of extendedParents.get(bead)) {
                if (pos.has(p)) {
                    newLines.push({ p: pos.get(p), c: beadPos });
                }
            }
            for (const c of extendedChildren.get(bead)) {
                if (pos.has(c)) {
                    newLines.push({ p: beadPos, c: pos.get(c) });
                }
            }

            // If there are no intersections of a parent-child edge with any middle bead, break
            let intersects = false;
            for (const line of [...lines, ...newLines]) {
                const [x1, y1] = line.p;
                const [x2, y2] = line.c;

                for (const [middleBead, [x3, y3]] of pos.entries()) {
                     if (intersection(x1, y1, x2, y2, x3, y3)) {
                         intersects = true;
                         break;
                     }
                }
                if (intersects) break;
            }

            if (!intersects) {
                lines.push(...newLines);
                break;
            }
        }
    } // End loop over remainingY beads

    const cohortTips = tips(parents, children); // Tips within the cohort sub-braid
    const tipsPos = new Map();
    for (const tip of cohortTips) {
        if (pos.has(tip)) {
            tipsPos.set(tip, pos.get(tip));
        }
    }

    return [pos, tipsPos];
}

// --- Load / Save ---

/**
 * Load a JSON file containing a braid description.
 * @param {string} filename - Path to the JSON file.
 * @returns {object} DAG object.
 * @throws {Error} If file not found or JSON is invalid.
 */
function loadBraid(filename) {
    try {
        const jsonData = fs.readFileSync(filename, 'utf8');
        const d = JSON.parse(jsonData);
        const dag = {};

        dag.description = d.description;
        // Convert keys to numbers and values to Sets of numbers for maps/sets
        dag.parents = new Map(Object.entries(d.parents || {}).map(([k, v]) => [parseInt(k), new Set(v.map(Number))]));
        // Ensure all parent keys exist even if they have no parents listed explicitly
        const allBeads = new Set(dag.parents.keys());
         for (const parentsSet of dag.parents.values()) {
             for (const p of parentsSet) allBeads.add(p);
         }
         // Also add beads mentioned in children, geneses, tips etc if parents map is incomplete
         for (const childrenSet of Object.values(d.children || {})) { for(const c of childrenSet) allBeads.add(c); }
         if (d.geneses) for(const g of d.geneses) allBeads.add(g);
         if (d.tips) for(const t of d.tips) allBeads.add(t);
         if (d.cohorts) for(const cohort of d.cohorts) for(const b of cohort) allBeads.add(b);
         if (d.highest_work_path) for(const b of d.highest_work_path) allBeads.add(b);
         if (d.bead_work) for(const k of Object.keys(d.bead_work)) allBeads.add(parseInt(k));
         if (d.work) for(const k of Object.keys(d.work)) allBeads.add(parseInt(k));


         for(const bead of allBeads) {
             if (!dag.parents.has(bead)) dag.parents.set(bead, new Set()); // Add bead with empty parent set if missing
         }


        dag.children = new Map(Object.entries(d.children || {}).map(([k, v]) => [parseInt(k), new Set(v.map(Number))]));
        dag.geneses = new Set((d.geneses || []).map(Number));
        dag.tips = new Set((d.tips || []).map(Number));
        dag.cohorts = (d.cohorts || []).map(c => new Set(c.map(Number)));
        dag.beadWork = d.bead_work ? new Map(Object.entries(d.bead_work).map(([k, v]) => [parseInt(k), v])) : new Map([...allBeads].map(b => [b, 1]));
         // Ensure all beads have beadWork entry
         for (const b of allBeads) if (!dag.beadWork.has(b)) dag.beadWork.set(b, FIXED_BEAD_WORK);

        dag.work = d.work ? new Map(Object.entries(d.work).map(([k, v]) => [parseInt(k), v])) : null; // Mark as null if missing
        dag.highestWorkPath = (d.highest_work_path || []).map(Number);

        // Optional: Recalculate derived fields if missing or potentially inconsistent
        if (!d.children || dag.children.size === 0) dag.children = reverse(dag.parents);
        // Ensure children map covers all beads
        for(const b of allBeads) if (!dag.children.has(b)) dag.children.set(b, new Set());

        if (!d.geneses || dag.geneses.size === 0) dag.geneses = geneses(dag.parents);
        if (!d.tips || dag.tips.size === 0) dag.tips = tips(dag.parents, dag.children);
        // Recalculate cohorts if missing or empty - this might be slow
        if (!d.cohorts || dag.cohorts.length === 0 || dag.cohorts.reduce((sum, c) => sum + c.size, 0) !== allBeads.size) {
             // console.log(`Recalculating cohorts for ${filename}`);
             dag.cohorts = Array.from(cohorts(dag.parents, dag.children));
        }
        // Recalculate work if missing
        if (!dag.work) {
             // console.log(`Recalculating work for ${filename}`);
             dag.work = descendantWork(dag.parents, dag.children, dag.beadWork, dag.cohorts);
        } else {
             // Ensure all beads have work entry
             for (const b of allBeads) if (!dag.work.has(b)) dag.work.set(b, dag.beadWork.get(b) || 0); // Base work if missing? Or recalculate fully? Let's just set base work.
        }
        // Recalculate HWP if missing or empty
        if (!d.highest_work_path || dag.highestWorkPath.length === 0) {
            // console.log(`Recalculating HWP for ${filename}`);
            dag.highestWorkPath = highestWorkPath(dag.parents, dag.children, dag.beadWork, dag.work);
        }


        return dag;
    } catch (err) {
        if (err.code === 'ENOENT') {
            throw new Error(`loadBraid could not open file: ${filename}`);
        } else if (err instanceof SyntaxError) {
            throw new Error(`Invalid JSON in file: ${filename} - ${err.message}`);
        } else {
            console.error(`Error loading braid from ${filename}:`, err); // Log other errors
            throw err; // Re-throw other errors
        }
    }
}

/**
 * Renumber beads sequentially starting from geneses using original hashes.
 * @param {Map<any, Set<any>>} hashedParents - Map of {beadHash: Set<parentHashes>}.
 * @returns {Map<number, Set<number>>} Map of {beadId: Set<parentId>}.
 */
function numberBeads(hashedParents) {
    let beadIdCounter = 0;
    const parents = new Map(); // { newId: Set<newParentId> }
    const beadIds = new BiMap(); // { hash: newId }
    const q = []; // Queue for BFS (using hash)

    // Initialize with geneses
    const initialGeneses = geneses(hashedParents); // Find geneses using the hash map
    const sortedGeneses = [...initialGeneses].sort(); // Sort for deterministic numbering if needed

    for (const beadHash of sortedGeneses) {
        if (!beadIds.has(beadHash)) {
            const newId = beadIdCounter++;
            beadIds.set(beadHash, newId);
            if (!parents.has(newId)) parents.set(newId, new Set()); // Ensure genesis exists
            q.push(beadHash); // Add hash to queue
        }
    }

    const hashedChildren = reverse(hashedParents); // { hash: Set<childHashes> }
    let head = 0;
    while(head < q.length) {
        const parentHash = q[head++]; // Get hash from queue
        if (!beadIds.has(parentHash)) continue; // Should not happen if added correctly
        const parentId = beadIds.get(parentHash);

        const childrenHashes = hashedChildren.get(parentHash) || new Set();
        const sortedChildrenHashes = [...childrenHashes].sort(); // Sort for deterministic numbering

        for(const childHash of sortedChildrenHashes) {
            let childId;
            let isNew = false;
            if (!beadIds.has(childHash)) {
                childId = beadIdCounter++;
                beadIds.set(childHash, childId);
                isNew = true;
            } else {
                childId = beadIds.get(childHash);
            }
             // Ensure child exists in parents map before adding parents to it
            if (!parents.has(childId)) {
                 parents.set(childId, new Set());
            }
            parents.get(childId).add(parentId);

            if(isNew) {
                q.push(childHash); // Add new hash to queue only if newly discovered
            }
        }
    }

    // Ensure all original hashes mentioned anywhere are included in the numbered graph
    const allHashes = new Set(hashedParents.keys());
     for(const pSet of hashedParents.values()) {
         for (const p of pSet) allHashes.add(p);
     }
     for (const hash of allHashes) {
         if (!beadIds.has(hash)) {
              // This indicates a disconnected component not starting from initial geneses
              // console.warn(`Hash ${hash} was not reached during numbering (possible disconnected component). Assigning new ID.`);
              const newId = beadIdCounter++;
              beadIds.set(hash, newId);
              if (!parents.has(newId)) parents.set(newId, new Set()); // Assume no parents if not reached

              // Find its original parents and add numbered links if parents were numbered
              const originalParents = hashedParents.get(hash);
              if (originalParents) {
                    for (const pHash of originalParents) {
                        if (beadIds.has(pHash)) {
                            parents.get(newId).add(beadIds.get(pHash));
                        }
                    }
              }
         }
     }


    return parents;
}


/**
 * Save a braid structure to a JSON file. Calculates derived properties.
 * @param {Map<number, Set<number>>} parents - The numbered parent map.
 * @param {string} filename - Path to save the file.
 * @param {string} [description] - Optional description.
 * @param {Map<number, number>} [beadWork] - Optional work map (if not provided, uses default).
 * @returns {object} The generated DAG object that was saved.
 * @throws {Error} If file writing fails.
 */
function saveBraid(parents, filename, description = null, beadWork = null) {
    // Calculate all derived properties based on the numbered parents
    const dag = {};
    dag.description = description;
    dag.parents = parents; // Map<number, Set<number>>
    dag.children = reverse(parents); // Map<number, Set<number>>
    dag.geneses = geneses(parents); // Set<number>
    dag.tips = tips(parents, dag.children); // Set<number>
    dag.cohorts = Array.from(cohorts(parents, dag.children)); // Array<Set<number>>
    // Use provided beadWork or default, ensuring all parent keys have work
    const finalBeadWork = new Map(beadWork);
    for(const beadId of parents.keys()) {
        if (!finalBeadWork.has(beadId)) {
            finalBeadWork.set(beadId, FIXED_BEAD_WORK);
        }
    }
    dag.beadWork = finalBeadWork; // Map<number, number>

    dag.work = descendantWork(parents, dag.children, dag.beadWork, dag.cohorts); // Map<number, number>
    dag.highestWorkPath = highestWorkPath(parents, dag.children, dag.beadWork, dag.work); // Array<number>


    // Prepare data for JSON serialization (convert Sets to Arrays, Maps to Objects, sort for consistency)
    const serializableDag = {
        description: dag.description,
        parents: Object.fromEntries([...dag.parents.entries()].sort(([k1],[k2])=>k1-k2).map(([k, v]) => [k, [...v].sort((a,b)=>a-b)])),
        children: Object.fromEntries([...dag.children.entries()].sort(([k1],[k2])=>k1-k2).map(([k, v]) => [k, [...v].sort((a,b)=>a-b)])),
        geneses: [...dag.geneses].sort((a,b)=>a-b),
        tips: [...dag.tips].sort((a,b)=>a-b),
        cohorts: dag.cohorts.map(c => [...c].sort((a,b)=>a-b)),
        bead_work: Object.fromEntries([...dag.beadWork.entries()].sort(([k1],[k2])=>k1-k2)),
        work: Object.fromEntries([...dag.work.entries()].sort(([k1],[k2])=>k1-k2)),
        highest_work_path: dag.highestWorkPath
    };

    try {
        // Use path.join for better cross-platform compatibility
        const fullPath = path.resolve(filename);
        // Ensure directory exists (optional, depending on requirements)
        fs.mkdirSync(path.dirname(fullPath), { recursive: true });

        fs.writeFileSync(fullPath, JSON.stringify(serializableDag, null, 4), 'utf8');
        // console.log(`Braid saved to ${fullPath}`);
        return dag; // Return the computed dag object
    } catch (err) {
        throw new Error(`Failed to save braid to ${filename}: ${err.message}`);
    }
}

// Example Usage (if run directly, e.g., using node braid.js)
if (require.main === module) {
    console.log("Braid library loaded. Running example...");
    // Example: Create a simple braid and save it
    const exampleHashedParents = new Map([
        ['g1', new Set()], // Genesis 1
        ['g2', new Set()], // Genesis 2
        ['a', new Set(['g1'])],
        ['b', new Set(['g1', 'g2'])],
        ['c', new Set(['a', 'b'])],
        ['d', new Set(['c'])] // Tip
    ]);

    console.log("Original Hashed Parents:", exampleHashedParents);

    try {
        const numberedParents = numberBeads(exampleHashedParents);
        console.log("\nNumbered Parents Map:", numberedParents);

        const savedDag = saveBraid(numberedParents, 'test_braid.json', 'Simple Test Braid');
        console.log("\nSaved DAG Description:", savedDag.description);
        console.log("Saved DAG Geneses:", savedDag.geneses);
        console.log("Saved DAG Tips:", savedDag.tips);
        console.log("Saved DAG Cohorts:", savedDag.cohorts);
        console.log("Saved DAG HWP:", savedDag.highestWorkPath);

        console.log("\nLoading DAG back from file...");
        const loadedDag = loadBraid('test_braid.json');
        console.log("Loaded DAG Description:", loadedDag.description);
        console.log("Loaded Geneses:", loadedDag.geneses);
        console.log("Loaded Tips:", loadedDag.tips);
        console.log("Loaded Cohorts:", loadedDag.cohorts);
        console.log("Loaded HWP:", loadedDag.highestWorkPath);
        console.log("Loaded Work:", loadedDag.work);

    } catch (error) {
        console.error("\nError during example execution:", error);
    }
}


// Export functions for use as a module
module.exports = {
    makeDag,
    geneses,
    tips,
    reverse,
    generation,
    allAncestors,
    cohorts,
    cohortTail,
    cohortHead,
    subBraid,
    descendantWork,
    beadCompare,
    workSortComparator,
    highestWorkPath,
    layout,
    loadBraid,
    numberBeads,
    saveBraid,
    BiMap, // Export helper class if needed externally
    FIXED_BEAD_WORK,
    TEST_CASE_DIR
};
