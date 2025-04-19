import * as PIXI from 'pixi.js';
import { GraphNode, Position } from '../BraidPoolDAGTypes';
import { setupNodeInteractivity } from './EventHandlers';

/**
 * Creates a node graphic for the graph visualization
 * @param nodeData Node data to visualize
 * @param position Position coordinates
 * @param isHighlighted Whether node is highlighted (part of highest work path)
 * @param onClick Click handler callback
 * @returns PIXI.Graphics object representing the node
 */
export const createNodeGraphic = (
  nodeData: GraphNode,
  position: Position,
  isHighlighted: boolean,
  onClick: (nodeId: string, data: any) => void
): PIXI.Graphics => {
  // Create node circle
  const circle = new PIXI.Graphics();

  // Determine node appearance based on type
  const nodeSize = isHighlighted ? 8 : 5;
  const fillColor = isHighlighted ? 0x4a90e2 : 0xdddddd;
  const lineColor = isHighlighted ? 0x2a6fb2 : 0x999999;

  // Draw the node with version-safe approach
  circle.clear();

  // Use try/catch to handle different PIXI versions gracefully
  try {
    // Standard line style (works in all versions)
    circle.setStrokeStyle({
      width: 1,
      color: lineColor,
      alpha: 1,
    });
    circle.fill(fillColor);
    circle.circle(0, 0, nodeSize);

    console.log(`⚪ [PIXI] Drew node ${nodeData.id}`);
  } catch (err) {
    console.error('⚠️ [PIXI] Error drawing node:', err);
  }

  // Position the node
  circle.position.set(position.x, position.y);

  // Setup interactivity
  setupNodeInteractivity(circle, nodeData, onClick);

  return circle;
};

/**
 * Creates a line connecting two nodes in the graph
 * @param sourcePos Source node position
 * @param targetPos Target node position
 * @param isHighlighted Whether this connection is highlighted
 * @returns PIXI.Graphics object representing the line
 */
export const createEdgeGraphic = (
  sourcePos: Position,
  targetPos: Position,
  isHighlighted: boolean
): PIXI.Graphics => {
  // Create a line
  const line = new PIXI.Graphics();

  try {
    // Use standard API that works in all PIXI versions
    if (isHighlighted) {
      // Highest work path - make it prominent
      line.setStrokeStyle({
        width: 3,
        color: 0x4a90e2,
        alpha: 1,
      });
    } else {
      // Regular edge
      line.setStrokeStyle({
        width: 1,
        color: 0xaaaaaa,
        alpha: 0.8,
      });
    }

    line.moveTo(sourcePos.x, sourcePos.y);
    line.lineTo(targetPos.x, targetPos.y);

    console.log(`🔗 [PIXI] Drew edge ${isHighlighted ? '(highlighted)' : ''}`);
  } catch (err) {
    console.error('⚠️ [PIXI] Error drawing edge:', err);
  }

  return line;
};

/**
 * Renders all edges between nodes in the graph
 * @param nodeList List of all nodes
 * @param positions Map of node positions
 * @param hwpSet Set of node IDs in the highest work path
 * @param container Container to add edges to
 * @returns Number of edges drawn
 */
export const renderEdges = (
  nodeList: GraphNode[],
  positions: Record<string, Position>,
  hwpSet: Set<string>,
  container: PIXI.Container
): number => {
  console.log('🔗 [PIXI] Drawing links...');

  if (!container) {
    console.error('🔍 [DEBUG] Invalid links container');
    return 0;
  }

  // Clear existing edges
  container.removeChildren();

  // Track edges we've already drawn to avoid duplicates
  const drawnEdges = new Set<string>();
  let edgeCount = 0;

  nodeList.forEach((node) => {
    const sourcePos = positions[node.id];
    if (!sourcePos) return;

    node.parents.forEach((parentId) => {
      const targetPos = positions[parentId];
      if (!targetPos) return;

      // Avoid drawing the same edge twice
      const edgeId = `${node.id}-${parentId}`;
      const reverseEdgeId = `${parentId}-${node.id}`;
      if (drawnEdges.has(edgeId) || drawnEdges.has(reverseEdgeId)) return;
      drawnEdges.add(edgeId);

      // Determine if this is a highest work path edge
      const isHWP = hwpSet.has(node.id) && hwpSet.has(parentId);

      // Create the edge graphic
      const line = createEdgeGraphic(sourcePos, targetPos, isHWP);

      // Add to container
      container.addChild(line);
      edgeCount++;
    });
  });

  console.log(`🔗 [PIXI] Drew ${edgeCount} edges`);
  return edgeCount;
};

/**
 * Renders all nodes in the graph
 * @param nodeList List of all nodes
 * @param positions Map of node positions
 * @param hwpSet Set of node IDs in the highest work path
 * @param container Container to add nodes to
 * @param onNodeClick Callback when a node is clicked
 * @returns Number of nodes drawn
 */
export const renderNodes = (
  nodeList: GraphNode[],
  positions: Record<string, Position>,
  hwpSet: Set<string>,
  container: PIXI.Container,
  onNodeClick: (nodeId: string, nodeData: GraphNode) => void
): number => {
  console.log('⚪ [PIXI] Drawing nodes...');

  if (!container) {
    console.error('🔍 [DEBUG] Invalid nodes container');
    return 0;
  }

  // Clear existing nodes
  container.removeChildren();
  let nodeCount = 0;

  // Track boundaries to help with viewport positioning
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;

  nodeList.forEach((node) => {
    const pos = positions[node.id];
    if (!pos) return;

    // Update boundaries
    minX = Math.min(minX, pos.x);
    minY = Math.min(minY, pos.y);
    maxX = Math.max(maxX, pos.x);
    maxY = Math.max(maxY, pos.y);

    // Determine if this node is in the highest work path
    const isHWP = hwpSet.has(node.id);

    // Create the node graphic
    const circle = createNodeGraphic(node, pos, isHWP, onNodeClick);

    // Add to container
    container.addChild(circle);
    nodeCount++;
  });

  console.log(`⚪ [PIXI] Drew ${nodeCount} nodes`);

  // Log boundaries to help with debugging
  if (nodeCount > 0) {
    console.log(
      `📊 [PIXI] Graph boundaries: x(${minX}→${maxX}) y(${minY}→${maxY})`
    );

    // Store boundaries directly on container as properties instead of userData
    (container as any).graphBoundaries = { minX, minY, maxX, maxY };
    (container as any).graphWidth = maxX - minX;
    (container as any).graphHeight = maxY - minY;
  }

  return nodeCount;
};

/**
 * Process graph data from API into a node list
 * @param graphData Raw graph data from API
 * @returns List of graph nodes
 */
export const processGraphData = (
  graphData: any
): { nodeList: GraphNode[]; hwpSet: Set<string> } => {
  const nodeList: GraphNode[] = [];
  const hwpSet = new Set<string>(graphData.highest_work_path || []);

  if (graphData?.parents) {
    Object.keys(graphData.parents).forEach((nodeId) => {
      nodeList.push({
        id: nodeId,
        parents: graphData.parents[nodeId] || [],
        children: graphData.children[nodeId] || [],
        work: graphData.work ? graphData.work[nodeId] : undefined,
      });
    });
  }

  return { nodeList, hwpSet };
};

export default {
  createNodeGraphic,
  createEdgeGraphic,
  renderEdges,
  renderNodes,
  processGraphData,
};
