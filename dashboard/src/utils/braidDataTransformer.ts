import {
  BraidData,
  BraidNode,
  BraidLink,
  BraidVisualizationData,
} from '../types/braid';

export const transformBraidData = (data: BraidData): BraidVisualizationData => {
  const nodes: BraidNode[] = [];
  const links: BraidLink[] = [];

  // Convert nodes from parents data
  Object.entries(data.parents).forEach(([id, parents]) => {
    const nodeId = parseInt(id);
    const children = data.children[id] || [];

    // Determine which cohort this node belongs to
    let cohortIndex = -1;
    for (let i = 0; i < data.cohorts.length; i++) {
      if (data.cohorts[i].includes(nodeId)) {
        cohortIndex = i;
        break;
      }
    }

    nodes.push({
      id: nodeId,
      parents: parents,
      children: children,
      cohort: cohortIndex,
      isTip: data.tips.includes(nodeId),
    });

    // Create links from this node to its parents
    parents.forEach((parentId) => {
      links.push({
        source: nodeId,
        target: parentId,
      });
    });
  });

  // Sort nodes by id for consistent rendering
  nodes.sort((a, b) => a.id - b.id);

  // Calculate high-work path (simplified version)
  // In a real implementation, this would use the algorithm from the Python code
  const highWorkPath = calculateHighWorkPath(data);

  // Mark links that are part of the high work path
  links.forEach((link) => {
    if (
      highWorkPath.some(
        (pair) => pair[0] === link.source && pair[1] === link.target
      )
    ) {
      link.isHighWorkPath = true;
    }
  });

  return {
    nodes,
    links,
    cohorts: data.cohorts,
  };
};

// Simplified high work path calculation - in real implementation,
// this would use the same algorithm as in the Python code
const calculateHighWorkPath = (data: BraidData): [number, number][] => {
  const path: [number, number][] = [];

  // Simple approach: Follow the path from the tip with the highest id
  // to the genesis (node 0) choosing the first parent at each step
  const sortedTips = [...data.tips].sort((a, b) => b - a);
  if (sortedTips.length === 0) return path;

  let currentNode = sortedTips[0];

  while (currentNode !== 0) {
    const parents = data.parents[currentNode.toString()];
    if (!parents || parents.length === 0) break;

    const nextNode = parents[0]; // Choose first parent
    path.push([currentNode, nextNode]);
    currentNode = nextNode;
  }

  return path;
};

// Parse sample data file for direct usage
export const loadSampleBraidData = (): BraidData => {
  // In a real app, this would be loaded via import or fetch
  const sampleData = require('../data/my_test_braid.json');

  // Ensure we have cohorts and tips
  if (!sampleData.cohorts) {
    // Generate cohorts if not present in data
    sampleData.cohorts = generateCohorts(sampleData.parents);
  }

  if (!sampleData.tips) {
    // Generate tips as nodes with no children
    sampleData.tips = findTips(sampleData.parents, sampleData.children);
  }

  return sampleData as BraidData;
};

// Utility function to find tips (nodes with no children)
const findTips = (
  parents: Record<string, number[]>,
  children: Record<string, number[]>
): number[] => {
  return Object.keys(parents)
    .filter((id) => !children[id] || children[id].length === 0)
    .map((id) => parseInt(id));
};

// Simple cohort generation algorithm (placeholder)
// A real implementation would use the algorithm from the Python code
const generateCohorts = (parents: Record<string, number[]>): number[][] => {
  const cohorts: number[][] = [];
  const processed = new Set<number>();

  // Start with genesis (node 0)
  cohorts.push([0]);
  processed.add(0);

  // Simple breadth-first traversal to form cohorts
  let currentCohort: number[] = [];

  Object.entries(parents).forEach(([id, parentIds]) => {
    const nodeId = parseInt(id);
    if (nodeId === 0 || processed.has(nodeId)) return;

    // If all parents are processed, add to current cohort
    const allParentsProcessed = parentIds.every((parentId) =>
      processed.has(parentId)
    );

    if (allParentsProcessed) {
      currentCohort.push(nodeId);
      processed.add(nodeId);
    }

    // Start a new cohort when current one reaches a certain size
    if (currentCohort.length >= 5) {
      cohorts.push([...currentCohort]);
      currentCohort = [];
    }
  });

  // Add any remaining nodes
  if (currentCohort.length > 0) {
    cohorts.push(currentCohort);
  }

  return cohorts;
};
