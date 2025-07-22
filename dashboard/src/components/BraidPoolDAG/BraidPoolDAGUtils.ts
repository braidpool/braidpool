import * as d3 from 'd3';
import { GraphNode, Position } from './Types';

export function layoutNodes(
  allNodes: GraphNode[],
  hwPath: string[],
  beadWork: Record<string, number> = {},
  previousCohortTips: Record<string, Position> = {},
  width: number = 1200,
  margin: { top: number; right: number; bottom: number; left: number } = {
    top: 0,
    right: 0,
    bottom: 0,
    left: 50,
  },
  COLUMN_WIDTH: number = 200,
  VERTICAL_SPACING: number = 150
): Record<string, Position> {
  const positions: Record<string, Position> = {};
  const hwPathSet = new Set(hwPath);
  const centerY = (width - margin.top) / 2 + margin.top + 500;
  const allParents: Record<string, Set<string>> = {};
  const allChildren: Record<string, Set<string>> = {};
  const workValues: Record<string, number> = {};

  allNodes.forEach((node) => {
    allParents[node.id] = new Set(node.parents);
    workValues[node.id] = beadWork[node.id] || 1;
    node.parents.forEach((parent) => {
      if (!allChildren[parent]) allChildren[parent] = new Set();
      allChildren[parent].add(node.id);
    });
  });

  // intersection logic
  const doesIntersect = (
    lineStart: Position,
    lineEnd: Position,
    point: Position
  ): boolean => {
    if (
      (lineStart.x === point.x && lineStart.y === point.y) ||
      (lineEnd.x === point.x && lineEnd.y === point.y)
    )
      return false;

    // Colinear check
    const crossProduct =
      (point.y - lineStart.y) * (lineEnd.x - lineStart.x) -
      (point.x - lineStart.x) * (lineEnd.y - lineStart.y);
    if (Math.abs(crossProduct) > Number.EPSILON) return false;

    // Bounding box check
    const isBetweenX = (point.x - lineStart.x) * (point.x - lineEnd.x) <= 0;
    const isBetweenY = (point.y - lineStart.y) * (point.y - lineEnd.y) <= 0;

    return isBetweenX && isBetweenY;
  };

  const proposedX: Record<string, number> = {};
  hwPath.forEach((bead, i) => (proposedX[bead] = i));

  const setXCoord = (bead: string) => {
    if (proposedX[bead] !== undefined) return;

    const parents = Array.from(allParents[bead] || []);
    const children = Array.from(allChildren[bead] || []);
    let minX = 0;

    if (!parents.length) {
      proposedX[bead] = 0;
      return;
    }

    parents.forEach((parent) => {
      setXCoord(parent);
      minX = Math.max(minX, proposedX[parent] + 1);
    });

    let maxX = Infinity;
    children.forEach((child) => {
      if (proposedX[child] !== undefined)
        maxX = Math.min(maxX, proposedX[child] - 1);
    });

    if (minX > maxX && maxX < Infinity) {
      children.forEach((child) => {
        if (proposedX[child] !== undefined && proposedX[child] <= minX) {
          const shift = minX + 1 - proposedX[child];
          Object.keys(proposedX).forEach((k) => {
            if (proposedX[k] >= proposedX[child]) proposedX[k] += shift;
          });
        }
      });
    }

    proposedX[bead] = minX;
  };

  // Process non-HW nodes
  allNodes.filter((n) => !hwPathSet.has(n.id)).forEach((n) => setXCoord(n.id));

  // Adjust tail nodes (no children)
  const maxX = Math.max(...Object.values(proposedX));
  allNodes.forEach((n) => {
    if ((!n.children || n.children.length === 0) && !hwPathSet.has(n.id)) {
      proposedX[n.id] = maxX;
    }
  });

  // Ensure HW path order
  for (let i = 0; i < hwPath.length - 1; i++) {
    if (proposedX[hwPath[i]] >= proposedX[hwPath[i + 1]]) {
      proposedX[hwPath[i + 1]] = proposedX[hwPath[i]] + 1;
    }
  }

  // Position HW path nodes
  hwPath.forEach((bead) => {
    positions[bead] = {
      x: margin.left + proposedX[bead] * COLUMN_WIDTH,
      y: centerY,
    };
  });

  // Add previous cohort tips
  Object.entries(previousCohortTips).forEach(([id, pos]) => {
    positions[id] = { x: margin.left - COLUMN_WIDTH, y: pos.y };
  });

  // Python-style spiral placement
  const remainingNodes = allNodes
    .filter((n) => !hwPathSet.has(n.id))
    .sort((a, b) => workValues[a.id] - workValues[b.id]) // Ascending sort
    .reverse(); // Python's reverse=True

  const lines: Array<[Position, Position]> = [];

  remainingNodes.forEach((node) => {
    const bead = node.id;
    const baseX = margin.left + proposedX[bead] * COLUMN_WIDTH;
    let currentY = centerY;
    let distance = 0;
    let direction = 1;

    while (true) {
      currentY = centerY + direction * distance * VERTICAL_SPACING;
      direction *= -1;
      if (direction === 1) distance++;

      // Check collisions
      const collides = Object.values(positions).some(
        (pos) =>
          Math.abs(pos.x - baseX) < COLUMN_WIDTH / 2 &&
          Math.abs(pos.y - currentY) < VERTICAL_SPACING / 2
      );

      if (collides) continue;

      const tempPos = { x: baseX, y: currentY };
      positions[bead] = tempPos;

      // Generate connections
      const connections: Array<[Position, Position]> = [];
      (allParents[bead] || []).forEach((parent) => {
        if (positions[parent]) connections.push([positions[parent], tempPos]);
      });
      (allChildren[bead] || []).forEach((child) => {
        if (positions[child]) connections.push([tempPos, positions[child]]);
      });

      // intersection check
      const hasBadLine = connections.some(([start, end]) =>
        Object.entries(positions).some(
          ([otherId, pos]) =>
            otherId !== bead && doesIntersect(start, end, pos as Position)
        )
      );

      if (!hasBadLine) {
        lines.push(...connections);
        break;
      }
    }
  });

  return positions;
}

export function getEllipseEdgePoint(
  src: Position,
  tgt: Position,
  rx: number,
  ry: number
): Position {
  const dx = tgt.x - src.x;
  const dy = tgt.y - src.y;
  const len = Math.sqrt(dx * dx + dy * dy);

  // Normalize the direction vector
  const nx = dx / len;
  const ny = dy / len;

  // Scale using ellipse radii
  const scale = 1 / Math.sqrt((nx * nx) / (rx * rx) + (ny * ny) / (ry * ry));

  return {
    x: src.x + nx * scale,
    y: src.y + ny * scale,
  };
}

export function animateLinkDirection(selection: any) {
  selection
    .attr('stroke-dasharray', '5,5') // dashed stroke
    .attr('stroke-dashoffset', 10) // initial offset
    .transition()
    .duration(1000)
    .ease(d3.easeLinear)
    .attr('stroke-dashoffset', 0) // animate offset to 0
    .on('end', function repeat(this: any) {
      // @ts-ignore
      import('d3').then((d3) => {
        d3.select(this)
          .attr('stroke-dashoffset', 10)
          .transition()
          .duration(1000)
          .ease(d3.easeLinear)
          .attr('stroke-dashoffset', 0)
          .on('end', repeat);
      });
    });
}
