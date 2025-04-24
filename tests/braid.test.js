const fs = require('fs');
const path = require('path');
const Braid = require('./braid.js'); // Assuming braid.js is in the same directory

// Destructure necessary functions from the imported module
const {
    geneses,
    tips,
    reverse,
    cohorts,
    highestWorkPath,
    descendantWork,
    subBraid,
    cohortHead,
    cohortTail,
    loadBraid,
    allAncestors, // Assuming iterative version
    // checkCohort, // Skipped - Function not implemented in braid.js based on provided source
    TEST_CASE_DIR
} = Braid;

// Helper to convert simple object representation to Map<number, Set<number>>
function createParentsMap(obj) {
    const map = new Map();
    for (const key in obj) {
        const beadId = parseInt(key);
        const parentIds = new Set(obj[key].map(Number));
        map.set(beadId, parentIds);
    }
    // Ensure all mentioned parent IDs also exist as keys, even if they have no parents listed
    const allBeads = new Set(map.keys());
    for (const parentsSet of map.values()) {
        for (const p of parentsSet) {
            allBeads.add(p);
        }
    }
    for (const bead of allBeads) {
        if (!map.has(bead)) {
            map.set(bead, new Set());
        }
    }
    return map;
}

// --- Test Data ---
const parents1 = createParentsMap({0: [], 1: [0], 2: [1], 3: [2]}); // blockchain
const parents2 = createParentsMap({0: [], 1: [], 2: [1], 3: [1]});
const parents3 = createParentsMap({0: [], 1: [], 2: [], 3: [1], 4: [0]});
const parents4 = createParentsMap({0: [], 1: [], 2: [], 3: [0, 1, 2], 4: [0, 1, 2], 5: [0, 1, 2]});
const diamond = createParentsMap({0: [], 1: [0], 2: [0], 3: [1, 2], 4: [3]});

// --- Test Suites ---

describe('Braid Utility Functions', () => {

    // --- Geneses Tests ---
    describe('geneses', () => {
        test('should find single genesis in blockchain', () => {
            expect(geneses(parents1)).toEqual(new Set([0]));
        });

        test('should find multiple geneses', () => {
            expect(geneses(parents2)).toEqual(new Set([0, 1]));
        });

        test('should find multiple geneses case 2', () => {
            expect(geneses(parents3)).toEqual(new Set([0, 1, 2]));
        });

        test('should find single genesis in loaded files', () => {
            const files = fs.readdirSync(TEST_CASE_DIR).filter(f => f.endsWith(".json"));
            expect(files.length).toBeGreaterThan(0); // Make sure files exist
            for (const filename of files.sort()) {
                const dag = loadBraid(path.join(TEST_CASE_DIR, filename));
                // Most test files seem to assume a single genesis 0 after numbering
                expect(geneses(dag.parents)).toEqual(new Set([0]));
            }
        });
    });

    // --- Tips Tests ---
    describe('tips', () => {
        test('should find single tip in blockchain', () => {
            expect(tips(parents1)).toEqual(new Set([3]));
        });

        test('should find multiple tips', () => {
            expect(tips(parents2)).toEqual(new Set([0, 2, 3])); // Bead 0 is also a tip here
        });

         test('should find multiple tips case 2', () => {
             // Recalculate parents3 tips correctly
             // 0 -> 4
             // 1 -> 3
             // 2 -> (none)
             // Tips are 2, 3, 4
            expect(tips(parents3)).toEqual(new Set([2, 3, 4]));
        });

        test('should find multiple tips case 3', () => {
            expect(tips(parents4)).toEqual(new Set([3, 4, 5]));
        });
    });

    // --- Reverse Tests ---
    describe('reverse', () => {
        test('should correctly reverse parent map', () => {
            const expectedChildren = createParentsMap({
                0: [3, 4, 5],
                1: [3, 4, 5],
                2: [3, 4, 5],
                3: [],
                4: [],
                5: []
            });
            expect(reverse(parents4)).toEqual(expectedChildren);
        });

         test('should correctly reverse diamond', () => {
            const expectedChildren = createParentsMap({
                0: [1, 2],
                1: [3],
                2: [3],
                3: [4],
                4: []
            });
            expect(reverse(diamond)).toEqual(expectedChildren);
        });
    });

    // --- Cohorts Tests ---
    describe('cohorts', () => {
        test('should find correct cohorts for blockchain', () => {
            const expectedCohorts = [new Set([0]), new Set([1]), new Set([2]), new Set([3])];
            expect(Array.from(cohorts(parents1))).toEqual(expectedCohorts);
        });

         test('should find correct cohorts for diamond', () => {
            const expectedCohorts = [new Set([0]), new Set([1,2]), new Set([3]), new Set([4])];
             const calculatedCohorts = Array.from(cohorts(diamond));
             // console.log("Calculated Diamond Cohorts:", calculatedCohorts); // Debugging
            expect(calculatedCohorts).toEqual(expectedCohorts);
        });

        test('should match cohorts from loaded files', () => {
            const files = fs.readdirSync(TEST_CASE_DIR).filter(f => f.endsWith(".json"));
            expect(files.length).toBeGreaterThan(0);
            for (const filename of files.sort()) {
                const filePath = path.join(TEST_CASE_DIR, filename);
                try {
                    const dag = loadBraid(filePath);
                    const calculatedCohorts = Array.from(cohorts(dag.parents, dag.children)); // Pass children for potential efficiency
                    // console.log(`File: ${filename}, Expected:`, dag.cohorts, "Calculated:", calculatedCohorts); // Debugging
                    expect(calculatedCohorts).toEqual(dag.cohorts);
                } catch (e) {
                    console.error(`Error processing file ${filename}:`, e);
                    throw e; // Fail test on error
                }
            }
        });

        test('should match reversed cohorts from loaded files', () => {
            const files = fs.readdirSync(TEST_CASE_DIR).filter(f => f.endsWith(".json"));
            expect(files.length).toBeGreaterThan(0);
            for (const filename of files.sort()) {
                 const filePath = path.join(TEST_CASE_DIR, filename);
                try {
                    const dag = loadBraid(filePath);
                    const reversedParents = reverse(dag.parents); // Children become parents
                    const expectedReversedCohorts = [...dag.cohorts].reverse(); // Reverse the order of cohorts

                    const calculatedReversedCohorts = Array.from(cohorts(reversedParents)); // Calculate cohorts on reversed graph

                    console.log(`File: ${filename} (Reversed), Expected:`, expectedReversedCohorts, "Calculated:", calculatedReversedCohorts); // Debugging

                    // Compare cohorts element by element if direct comparison fails due to Set ordering within arrays
                    expect(calculatedReversedCohorts.length).toEqual(expectedReversedCohorts.length);
                    for(let i = 0; i < calculatedReversedCohorts.length; i++) {
                        expect(calculatedReversedCohorts[i]).toEqual(expectedReversedCohorts[i]);
                    }
                } catch (e) {
                    console.error(`Error processing reversed file ${filename}:`, e);
                    throw e; // Fail test on error
                }
            }
        });
    });

     // --- Highest Work Path Tests ---
    describe('highestWorkPath', () => {
        test('should find correct HWP for blockchain', () => {
            expect(highestWorkPath(parents1)).toEqual([0, 1, 2, 3]);
        });

         test('should find correct HWP for diamond', () => {
             // Depends on tie-breaking (bead ID). Assuming 1 < 2.
             // Path: 0 -> 1 -> 3 -> 4 OR 0 -> 2 -> 3 -> 4
             // Default beadCompare prefers lower ID in tie-break, so path through 1 maybe?
             // Let's trace: dWork(0)=5, dWork(1)=3, dWork(2)=3, dWork(3)=2, dWork(4)=1
             // aWork(0)=1, aWork(1)=2, aWork(2)=2, aWork(3)=4, aWork(4)=5
             // Compare 1 and 2: dWork same (3). aWork same (2). ID: 1 < 2. Comparator returns -1 (1 is "better").
             // So path should be 0 -> 1 -> 3 -> 4
            expect(highestWorkPath(diamond)).toEqual([0, 1, 3, 4]);
        });

        test('should match HWP from loaded files', () => {
            const files = fs.readdirSync(TEST_CASE_DIR).filter(f => f.endsWith(".json"));
            expect(files.length).toBeGreaterThan(0);
            for (const filename of files.sort()) {
                const filePath = path.join(TEST_CASE_DIR, filename);
                 try {
                    const dag = loadBraid(filePath);
                    const calculatedHWP = highestWorkPath(dag.parents, dag.children, dag.beadWork); // Use loaded work
                    expect(calculatedHWP).toEqual(dag.highestWorkPath);
                 } catch (e) {
                    console.error(`Error processing HWP for file ${filename}:`, e);
                    throw e; // Fail test on error
                }
            }
        });
    });

    // --- Descendant Work Tests ---
    describe('descendantWork', () => {
        test('should match work from loaded files', () => {
            const files = fs.readdirSync(TEST_CASE_DIR).filter(f => f.endsWith(".json"));
            expect(files.length).toBeGreaterThan(0);
            for (const filename of files.sort()) {
                 const filePath = path.join(TEST_CASE_DIR, filename);
                 try {
                    const dag = loadBraid(filePath);
                    const calculatedWork = descendantWork(dag.parents, dag.children, dag.beadWork, dag.cohorts);
                    // console.log(`File: ${filename}, Expected Work:`, dag.work, "Calculated Work:", calculatedWork); // Debugging
                    expect(calculatedWork).toEqual(dag.work);
                 } catch (e) {
                    console.error(`Error processing work for file ${filename}:`, e);
                    throw e; // Fail test on error
                }
            }
        });
    });

     // --- Sub Braid / Head / Tail Tests ---
    describe('subBraid, cohortHead, cohortTail', () => {
        test('should have consistent sub-braid boundaries (files)', () => {
            const files = fs.readdirSync(TEST_CASE_DIR).filter(f => f.endsWith(".json"));
            expect(files.length).toBeGreaterThan(0);
            for (const filename of files.sort()) {
                 const filePath = path.join(TEST_CASE_DIR, filename);
                 try {
                    const dag = loadBraid(filePath);
                    expect(dag.cohorts.length).toBeGreaterThan(0); // Ensure cohorts exist

                    for (const c of dag.cohorts) {
                         if (c.size === 0) continue; // Skip empty cohorts if they occur

                        const sub = subBraid(c, dag.parents);
                        const subGeneses = geneses(sub);
                        const subTips = tips(sub);
                        const head = cohortHead(c, dag.parents, dag.children);
                        const tail = cohortTail(c, dag.parents, dag.children);

                        // console.log(`File: ${filename}, Cohort: ${[...c]}, Head: ${[...head]}, SubGeneses: ${[...subGeneses]}`);
                        // console.log(`File: ${filename}, Cohort: ${[...c]}, Tail: ${[...tail]}, SubTips: ${[...subTips]}`);

                        expect(subGeneses).toEqual(head);
                        expect(subTips).toEqual(tail);

                        // Test cohort of sub-braid
                        const subCohorts = Array.from(cohorts(sub));
                        expect(subCohorts).toEqual([c]); // Sub-braid of a cohort should have only that cohort
                    }
                 } catch (e) {
                    console.error(`Error processing sub-braid for file ${filename}:`, e);
                    throw e; // Fail test on error
                }
            }
        });
    });

    // --- Ancestor Tests ---
    // describe('allAncestors', () => {
    //     // Test skipped: No recursive version available in JS to compare against.
    // });

});

// Add a simple check to ensure the TEST_CASE_DIR exists
if (!fs.existsSync(TEST_CASE_DIR) || !fs.lstatSync(TEST_CASE_DIR).isDirectory()) {
  console.error(`\nERROR: Test case directory "${TEST_CASE_DIR}" not found or is not a directory.`);
  console.error(`Please ensure the directory exists relative to the test execution path and contains .json braid files.\n`);
  // Optionally, exit the process if the directory is critical
  // process.exit(1);
}
