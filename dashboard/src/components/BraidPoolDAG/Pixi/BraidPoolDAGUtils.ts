import {
  GraphNode,
  NodeIdMapping,
  Position,
  GraphData,
  ConnectionStatus,
} from './BraidPoolDAGTypes';
import { io, Socket } from 'socket.io-client';

// Function to generate a unique color for each node (for picking)
let nextCol = 1;
export function genColor() {
  const ret = [];
  if (nextCol < 16777215) {
    ret.push(nextCol & 0xff); // R
    ret.push((nextCol & 0xff00) >> 8); // G
    ret.push((nextCol & 0xff0000) >> 16); // B
    nextCol += 1;
  }
  const col = 'rgb(' + ret.join(',') + ')';
  return col;
}

// Get socket URL helper function
export function getSocketUrl(): string {
  // Use the same approach as the working implementation
  return 'http://french.braidpool.net:65433/';
}

// Get fallback socket URL if primary fails
export function getFallbackSocketUrl(): string {
  return 'http://french.braidpool.net:65433/';
}

// Update the socket setup to emulate the working implementation
export function setupOptimizedSocket(
  onDataReceived: (data: GraphData) => void,
  onStatusChange: (status: ConnectionStatus) => void,
  onError: (message: string) => void
): Socket {
  const url = getSocketUrl();
  console.log('🔌 Connecting to socket server at:', url);

  // Modified socket options to address xhr poll error
  const socket = io(url, {
    reconnection: true,
    reconnectionAttempts: Infinity,
    reconnectionDelay: 1000,
    reconnectionDelayMax: 5000,
    timeout: 10000,
    transports: ['websocket'], // Force websocket only - avoid polling which is causing the error
    withCredentials: false, // Disable credentials for cross-domain requests
  });

  console.log('🔄 Starting connection attempt with websocket transport only');

  socket.on('connect', () => {
    console.log('🟢 Connected to Socket ', url);
    onStatusChange({
      connected: true,
      status: 'Connected',
      message: 'Connected to server. Requesting data...',
    });

    // Request data immediately after connecting
    console.log('📊 Sending data request');
    socket.emit('get-graph-data');
  });

  socket.on('disconnect', () => {
    console.log('🔴 Disconnected from Socket');
    onStatusChange({
      connected: false,
      status: 'Disconnected',
      message: 'Connection lost. Attempting to reconnect...',
    });
  });

  socket.on('connect_error', (err: Error) => {
    console.log('❌ Socket connection error:', err.message);
    onError(`Connection error: ${err.message}`);
  });

  socket.on('braid_update', (data: GraphData) => {
    console.log('📊 Received braid_update data!');
    onStatusChange({
      connected: true,
      status: 'Active',
      message: 'Data received successfully',
    });
    onDataReceived(data);
  });

  return socket;
}

// Layout calculation function
export const layoutNodesOptimized = (
  allNodes: GraphNode[],
  hwPath: string[],
  cohorts: string[][],
  selectedCohorts: number,
  width: number,
  height: number,
  margin: { top: number; right: number; bottom: number; left: number },
  COLUMN_WIDTH: number,
  VERTICAL_SPACING: number,
  cachedLayout: Record<string, Position> | null,
  cachedHwpLength: number,
  setCachedLayout: (layout: Record<string, Position>) => void,
  setCachedHwpLength: (length: number) => void
): Record<string, Position> => {
  console.log(
    `🧩 Laying out ${allNodes.length} nodes - using optimized approach. Limiting to ${selectedCohorts} cohorts.`
  );

  // Fast layout mode for large graphs (> 1000 nodes)
  const fastLayoutMode = allNodes.length > 1000;
  if (fastLayoutMode) {
    console.log('⚡ Using simplified layout for large graph');
  }

  // Only process cohorts we need (based on selected number to display)
  const visibleCohorts = cohorts.slice(-selectedCohorts);
  console.log(
    `📊 Showing latest ${selectedCohorts} cohorts out of ${cohorts.length} total cohorts`
  );

  // For performance, pre-calculate cohort map
  const cohortMap = new Map<string, number>();

  // Map all nodes to their cohorts
  visibleCohorts.forEach((cohort, index) => {
    cohort.forEach((nodeId) => cohortMap.set(nodeId, index));
  });

  // Create a set of all visible nodes to filter the graph
  const visibleNodeSet = new Set(visibleCohorts.flat());
  console.log(
    `👁️ Visible nodes: ${visibleNodeSet.size} out of ${allNodes.length} total nodes`
  );

  // Filter nodes to only include those in visible cohorts
  const visibleNodes = allNodes.filter((node) => visibleNodeSet.has(node.id));
  console.log(`🔍 Using ${visibleNodes.length} nodes for layout`);

  // Cache key should include selectedCohorts to ensure we regenerate when it changes
  const cacheKey = `${visibleNodes.length}-${hwPath.length}-${selectedCohorts}`;

  // Invalidate cache if number of cohorts changed
  if (
    cachedLayout &&
    Object.keys(cachedLayout).length === visibleNodes.length &&
    cachedHwpLength === hwPath.length
  ) {
    console.log('📑 Using cached layout - instant positioning');
    return cachedLayout;
  }

  // Create positions map
  const positions: Record<string, Position> = {};
  const columnOccupancy: Record<number, number> = {};
  const hwPathSet = new Set(hwPath);
  const centerY = height / 3;

  // We position the highest work path (HWP) first - this is the backbone
  // Only include HWP nodes that are in visible cohorts
  const visibleHwPath = hwPath.filter((id) => visibleNodeSet.has(id));
  console.log(
    `🔝 Visible HWP nodes: ${visibleHwPath.length} out of ${hwPath.length} total`
  );

  let currentX = margin.left;
  let prevCohort: number | undefined;
  const hwPathColumns: number[] = [];

  // Position visible HWP nodes
  visibleHwPath.forEach((nodeId, index) => {
    const currentCohort = cohortMap.get(nodeId);

    if (prevCohort !== undefined && currentCohort !== prevCohort) {
      currentX += COLUMN_WIDTH;
    }

    positions[nodeId] = { x: currentX, y: centerY };
    hwPathColumns.push(currentX);
    columnOccupancy[index] = 0;

    prevCohort = currentCohort;
    currentX += COLUMN_WIDTH;
  });

  // Process remaining visible non-HWP nodes
  const remainingNodes = visibleNodes.filter((node) => !hwPathSet.has(node.id));

  console.log(`⚙️ Processing ${remainingNodes.length} remaining visible nodes`);

  // Simplified generation system for faster performance
  if (fastLayoutMode) {
    // For large graphs, use simplified layout to improve performance
    const generations = new Map<string, number>();

    // Calculate generations in a single pass to avoid repeated calls
    remainingNodes.forEach((node) => {
      // If already calculated, skip
      if (generations.has(node.id)) return;

      const hwpParents = node.parents.filter(
        (p) => hwPathSet.has(p) && visibleNodeSet.has(p)
      );
      if (hwpParents.length > 0) {
        // If has HWP parent, directly compute generation from that
        generations.set(node.id, 1);
      } else {
        // Otherwise just put it one generation after its parents
        generations.set(node.id, 0);
      }
    });

    // Sort by generation for layout
    remainingNodes.sort(
      (a, b) => (generations.get(a.id) || 0) - (generations.get(b.id) || 0)
    );

    // Position nodes with simple layout algorithm for speed
    let rightmostX = Math.max(...hwPathColumns, 0) + COLUMN_WIDTH;
    let row = 0;
    const FAST_VERTICAL_SPACING = VERTICAL_SPACING * 0.8; // Tighter spacing for large graphs

    remainingNodes.forEach((node) => {
      const generation = generations.get(node.id) || 0;
      const column = generation + visibleHwPath.length;
      const colX = rightmostX + (column - visibleHwPath.length) * COLUMN_WIDTH;

      // Position in a grid-like structure for speed
      positions[node.id] = {
        x: colX,
        y: centerY + (row % 10) * FAST_VERTICAL_SPACING,
      };

      row++;
    });
  } else {
    // For smaller graphs, use more detailed layout algorithm
    const generations = new Map<string, number>();

    remainingNodes.forEach((node) => {
      const hwpParents = node.parents.filter(
        (p) => hwPathSet.has(p) && visibleNodeSet.has(p)
      );
      if (hwpParents.length > 0) {
        const minHWPIndex = Math.min(
          ...hwpParents.map((p) => visibleHwPath.indexOf(p))
        );
        generations.set(node.id, minHWPIndex + 1);
      } else {
        const visibleParents = node.parents.filter((p) =>
          visibleNodeSet.has(p)
        );
        const parentGens = visibleParents.map((p) => generations.get(p) || 0);
        generations.set(
          node.id,
          parentGens.length > 0 ? Math.max(...parentGens) + 1 : 0
        );
      }
    });

    remainingNodes.sort(
      (a, b) => (generations.get(a.id) || 0) - (generations.get(b.id) || 0)
    );

    const tipNodes: string[] = [];

    remainingNodes.forEach((node) => {
      if (node.parents.length === 1 && node.children.length === 0) {
        tipNodes.push(node.id);
      }

      const positionedParents = node.parents.filter(
        (p) => positions[p] && visibleNodeSet.has(p)
      );
      if (positionedParents.length === 0) return;

      const maxParentX = Math.max(
        ...positionedParents.map((p) => positions[p].x)
      );

      let targetX = maxParentX + COLUMN_WIDTH;

      const hwpParents = positionedParents.filter((p) => hwPathSet.has(p));
      if (hwpParents.length > 0) {
        const rightmostHWPParentX = Math.max(
          ...hwpParents.map((p) => positions[p].x)
        );
        const parentIndex = hwPathColumns.indexOf(rightmostHWPParentX);
        if (parentIndex >= 0 && parentIndex < hwPathColumns.length - 1) {
          targetX = hwPathColumns[parentIndex + 1];
        }
      }

      let yPos = centerY;
      const maxParentY = Math.max(
        ...positionedParents.map((p) => positions[p].y)
      );
      yPos = maxParentY + VERTICAL_SPACING;

      const colKey = Math.round((targetX - margin.left) / COLUMN_WIDTH);
      if (columnOccupancy[colKey] === undefined) {
        columnOccupancy[colKey] = 0;
      } else {
        yPos =
          maxParentY +
          VERTICAL_SPACING +
          columnOccupancy[colKey] * VERTICAL_SPACING;
      }
      columnOccupancy[colKey] += 1;

      positions[node.id] = {
        x: targetX,
        y: Math.min(yPos, Math.abs(height - yPos)),
      };
    });

    const maxColumnX = Math.max(
      ...Object.values(positions).map((pos) => pos.x),
      0
    );
    tipNodes.forEach((tipId) => {
      if (positions[tipId]) {
        positions[tipId].x = maxColumnX;
      }
    });
  }

  console.log(
    `🏁 Layout complete with ${Object.keys(positions).length} positioned nodes`
  );

  // Cache this layout for future use
  setCachedLayout(positions);
  setCachedHwpLength(hwPath.length);

  return positions;
};
