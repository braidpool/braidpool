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
export function renderEdges(
  nodeList: GraphNode[],
  positions: Record<string, Position>,
  hwpSet: Set<string>,
  container: PIXI.Container
): number {
  console.log('🔄 [PIXI] Rendering edges...');

  // Clear previous edges
  container.removeChildren();

  const regularEdgeColor = 0x48cae4; // Light blue
  const hwpEdgeColor = 0xff8500; // Orange
  const regularEdgeWidth = 1;
  const hwpEdgeWidth = 2;

  let edgesDrawn = 0;

  // Draw edges
  nodeList.forEach((node) => {
    // Skip if no position
    const sourcePos = positions[node.id];
    if (!sourcePos) return;

    // Draw edge to each child
    node.children.forEach((childId) => {
      const targetPos = positions[childId];
      if (!targetPos) return;

      // Determine if this is a HWP edge
      const isHwpEdge = hwpSet.has(node.id) && hwpSet.has(childId);
      const edgeColor = isHwpEdge ? hwpEdgeColor : regularEdgeColor;
      const edgeWidth = isHwpEdge ? hwpEdgeWidth : regularEdgeWidth;

      // Draw edge
      const line = new PIXI.Graphics();
      line.lineStyle(edgeWidth, edgeColor, 0.7); // Line with partial transparency
      line.moveTo(sourcePos.x, sourcePos.y);
      line.lineTo(targetPos.x, targetPos.y);

      // Add arrow
      /*
      const dx = targetPos.x - sourcePos.x;
      const dy = targetPos.y - sourcePos.y;
      const angle = Math.atan2(dy, dx);
      
      // Arrow head
      const arrowSize = 6;
      const arrowX = targetPos.x - Math.cos(angle) * 12; // Back from the tip
      const arrowY = targetPos.y - Math.sin(angle) * 12;
      
      line.beginFill(edgeColor);
      line.moveTo(
        arrowX - Math.cos(angle - Math.PI/6) * arrowSize,
        arrowY - Math.sin(angle - Math.PI/6) * arrowSize
      );
      line.lineTo(
        arrowX + Math.cos(angle) * arrowSize,
        arrowY + Math.sin(angle) * arrowSize
      );
      line.lineTo(
        arrowX - Math.cos(angle + Math.PI/6) * arrowSize,
        arrowY - Math.sin(angle + Math.PI/6) * arrowSize
      );
      line.endFill();
      */

      container.addChild(line);
      edgesDrawn++;
    });
  });

  console.log(`➡️ [PIXI] Drew ${edgesDrawn} edges`);
  return edgesDrawn;
}

/**
 * Renders all nodes in the graph
 * @param nodeList List of all nodes
 * @param positions Map of node positions
 * @param hwpSet Set of node IDs in the highest work path
 * @param container Container to add nodes to
 * @param onNodeClick Callback when a node is clicked
 * @returns Number of nodes drawn
 */
export function renderNodes(
  nodeList: GraphNode[],
  positions: Record<string, Position>,
  hwpSet: Set<string>,
  container: PIXI.Container,
  onNodeClick: (nodeId: string, nodeData: GraphNode) => void
): number {
  console.log('🎨 [PIXI] Rendering nodes...');

  // Clear previous nodes
  container.removeChildren();

  // First check if we need to render at all
  if (nodeList.length === 0) {
    console.warn('⚠️ No nodes to render');
    return 0;
  }

  // Track boundaries for viewport positioning
  let minX = Infinity,
    minY = Infinity;
  let maxX = -Infinity,
    maxY = -Infinity;

  // Precompute some values for performance
  const regularNodeSize = 10;
  const hwpNodeSize = 15;
  const regularColor = 0x48cae4; // Light blue
  const hwpColor = 0xff8500; // Orange
  const textStyle = new PIXI.TextStyle({
    fill: 0xffffff,
    fontSize: 10,
  });

  let nodesDrawn = 0;

  // Draw nodes
  nodeList.forEach((node) => {
    // Skip if position not defined
    const pos = positions[node.id];
    if (!pos) return;

    // Update boundaries
    minX = Math.min(minX, pos.x);
    minY = Math.min(minY, pos.y);
    maxX = Math.max(maxX, pos.x);
    maxY = Math.max(maxY, pos.y);

    // Create node graphics
    const isHwp = hwpSet.has(node.id);
    const nodeSize = isHwp ? hwpNodeSize : regularNodeSize;
    const nodeColor = isHwp ? hwpColor : regularColor;

    // Create node with graphics
    const graphics = new PIXI.Graphics();
    graphics.beginFill(nodeColor, 0.9); // Add slight transparency
    graphics.lineStyle(2, 0xffffff);
    graphics.drawCircle(0, 0, nodeSize);
    graphics.endFill();

    // Position
    graphics.position.set(pos.x, pos.y);

    // Set up interactivity
    graphics.eventMode = 'static';
    graphics.cursor = 'pointer';

    // Add click event
    graphics.on('pointerdown', () => {
      console.log(`🔍 Node clicked: ${node.id}`);
      onNodeClick(node.id, node);
    });

    // Add hover effect
    graphics.on('pointerover', () => {
      graphics.scale.set(1.2);
    });

    graphics.on('pointerout', () => {
      graphics.scale.set(1.0);
    });

    // Add node ID text
    const text = new PIXI.Text(String(nodesDrawn + 1), textStyle);
    text.anchor.set(0.5);
    graphics.addChild(text);

    // Add to container
    container.addChild(graphics);
    nodesDrawn++;

    if (nodesDrawn % 1000 === 0) {
      console.log(`🔄 Rendered ${nodesDrawn} nodes...`);
    }
  });

  // Store boundaries for later use in viewport positioning
  (container as any).graphBoundaries = { minX, minY, maxX, maxY };
  (container as any).graphWidth = maxX - minX;
  (container as any).graphHeight = maxY - minY;

  console.log(`⚪ [PIXI] Drew ${nodesDrawn} nodes`);
  console.log(
    `📊 [PIXI] Graph boundaries: x(${minX}→${maxX}) y(${minY}→${maxY})`
  );

  return nodesDrawn;
}

export function processGraphData(graphData: any, selectedCohorts: number) {
  console.log('🔄 [PIXI] Processing graph data...');
  console.log(
    `👁️ Limiting display to ${selectedCohorts} cohorts out of ${
      graphData.cohorts?.length || 0
    } total`
  );

  // Get only the selected number of cohorts (the latest ones)
  const visibleCohorts = (graphData.cohorts || []).slice(-selectedCohorts);

  // Create a set of visible nodes
  const visibleNodeSet = new Set(visibleCohorts.flat());
  console.log(
    `👁️ Visible nodes: ${visibleNodeSet.size} out of ${
      Object.keys(graphData.parents || {}).length
    } total`
  );

  // Convert graphData to node list format, filtering by visible nodes
  const nodeList: GraphNode[] = Object.keys(graphData.parents)
    .filter((id: string) => visibleNodeSet.has(id))
    .map((id: string) => ({
      id,
      parents: (graphData.parents[id] || []).filter((parentId: string) =>
        visibleNodeSet.has(parentId)
      ),
      children: (graphData.children[id] || []).filter((childId: string) =>
        visibleNodeSet.has(childId)
      ),
      work: graphData.work?.[id] || 0,
    }));

  // Create a filtered version of the highest work path
  const filteredHwp = (graphData.highest_work_path || []).filter((id: string) =>
    visibleNodeSet.has(id)
  );

  // Explicitly type the Set as string
  const hwpSet: Set<string> = new Set(filteredHwp);

  console.log(
    `✅ [PIXI] Processed ${nodeList.length} nodes from selected cohorts`
  );
  return { nodeList, hwpSet };
}
