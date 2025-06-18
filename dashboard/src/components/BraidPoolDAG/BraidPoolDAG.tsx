import React, { useRef, useEffect, useState } from 'react';
import * as d3 from 'd3';
import '../../App.css';
import { Loader } from 'lucide-react';
import { COLORS, GraphData, NodeIdMapping } from './Types';

const GraphVisualization: React.FC = () => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [graphData, setGraphData] = useState<GraphData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const width = window.innerWidth - 100;
  const margin = { top: 0, right: 0, bottom: 0, left: 50 }; // Changed top from 50 to 100
  const height = window.innerHeight - margin.top - margin.bottom;
  const [nodeIdMap, setNodeIdMap] = useState<NodeIdMapping>({});
  const [selectedCohorts, setSelectedCohorts] = useState<number | 'all'>(5);
  const nodeRadius = 30;
  const tooltipRef = useRef<HTMLDivElement>(null);
  var COLUMN_WIDTH = 200;
  const VERTICAL_SPACING = 150;

  // New state for the counter and the highlighted bead hash
  const [graphUpdateCounter, setGraphUpdateCounter] = useState(0);
  const [latestBeadHashForHighlight, setLatestBeadHashForHighlight] = useState<
    string | null
  >(null);

  interface Position {
    x: number;
    y: number;
  }

  interface GraphNode {
    id: string;
    parents: string[];
    children?: string[];
    work?: number;
  }

  const layoutNodes = (
    allNodes: GraphNode[],
    hwPath: string[],
    beadWork: Record<string, number> = {},
    previousCohortTips: Record<string, Position> = {}
  ): Record<string, Position> => {
    const positions: Record<string, Position> = {};
    const hwPathSet = new Set(hwPath);
    const centerY = (height - margin.top) / 2 + margin.top + 500;
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
    allNodes
      .filter((n) => !hwPathSet.has(n.id))
      .forEach((n) => setXCoord(n.id));

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
              otherId !== bead && doesIntersect(start, end, pos)
          )
        );

        if (!hasBadLine) {
          lines.push(...connections);
          break;
        }
      }
    });

    return positions;
  };

  const [_connectionStatus, setConnectionStatus] = useState('Disconnected');
  const prevFirstCohortRef = useRef<string[]>([]);
  const prevLastCohortRef = useRef<string[]>([]);

  const [totalBeads, setTotalBeads] = useState<number>(0);
  const [totalCohorts, setTotalCohorts] = useState<number>(0);
  const [maxCohortSize, setMaxCohortSize] = useState<number>(0);
  const [hwpLength, setHwpLength] = useState<number>(0);

  const [defaultZoom, setDefaultZoom] = useState(0.3);
  const zoomBehavior = useRef<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(
    null
  );

  useEffect(() => {
    const url = 'ws://localhost:65433/';
    const socket = new WebSocket(url);

    socket.onopen = () => {
      console.log('Connected to WebSocket', url);
      setConnectionStatus('Connected');
    };

    socket.onclose = () => {
      setConnectionStatus('Disconnected');
    };

    socket.onerror = (err) => {
      setConnectionStatus(`Error: ${err}`);
    };

    socket.onmessage = (event) => {
      try {
        const parsed = JSON.parse(event.data);
        const parsedData = parsed.data;

        if (!parsedData?.parents || typeof parsedData.parents !== 'object') {
          console.warn("Invalid 'parents' field in parsedData:", parsedData);
          return;
        }

        const children: Record<string, string[]> = {};
        if (parsedData?.parents && typeof parsedData.parents === 'object') {
          Object.entries(parsedData.parents).forEach(([nodeId, parents]) => {
            (parents as string[]).forEach((parentId) => {
              if (!children[parentId]) {
                children[parentId] = [];
              }
              children[parentId].push(nodeId);
            });
          });
        }

        const bead_count =
          parsedData?.parents && typeof parsedData.parents === 'object'
            ? Object.keys(parsedData.parents).length
            : 0;

        const graphData: GraphData = {
          highest_work_path: parsedData.highest_work_path,
          parents: parsedData.parents,
          cohorts: parsedData.cohorts,
          children,
          bead_count,
        };

        const firstCohortChanged =
          parsedData?.cohorts?.[0]?.length &&
          JSON.stringify(prevFirstCohortRef.current) !==
            JSON.stringify(parsedData.cohorts[0]);

        const lastCohortChanged =
          parsedData?.cohorts?.length > 0 &&
          JSON.stringify(prevLastCohortRef.current) !==
            JSON.stringify(parsedData.cohorts[parsedData.cohorts.length - 1]);

        if (firstCohortChanged) {
          const top = COLORS.shift();
          COLORS.push(top ?? `rgba(${217}, ${95}, ${2}, 1)`);
          prevFirstCohortRef.current = parsedData.cohorts[0];
        }

        if (lastCohortChanged) {
          prevLastCohortRef.current =
            parsedData.cohorts[parsedData.cohorts.length - 1];
        }

        const newMapping: NodeIdMapping = {};
        let nextId = 1;
        Object.keys(parsedData.parents).forEach((hash) => {
          if (!newMapping[hash]) {
            newMapping[hash] = nextId.toString();
            nextId++;
          }
        });

        setNodeIdMap(newMapping);
        setGraphData(graphData);

        // Increment the counter and update the highlighted bead hash
        setGraphUpdateCounter((prevCounter) => {
          const newCounter = prevCounter + 1;
          // If the counter is divisible by 100, set the latest bead's hash
          if (
            newCounter % 100 === 0 &&
            parsedData.highest_work_path.length > 0
          ) {
            const latestBeadHash =
              parsedData.highest_work_path[
                parsedData.highest_work_path.length - 1
              ];
            setLatestBeadHashForHighlight(latestBeadHash);
          }
          // The `latestBeadHashForHighlight` will remain set until the next time the condition is met.
          return newCounter;
        });

        setTotalBeads(bead_count);
        setTotalCohorts(parsedData.cohorts.length);
        setMaxCohortSize(
          Math.max(...parsedData.cohorts.map((c: string | any[]) => c.length))
        );
        setHwpLength(parsedData.highest_work_path.length);
        setLoading(false);

        // Trigger animation if cohorts changed
        if (firstCohortChanged || lastCohortChanged) {
          setTimeout(() => {
            animateCohorts(
              firstCohortChanged ? parsedData.cohorts[0] : [],
              lastCohortChanged
                ? parsedData.cohorts[parsedData.cohorts.length - 1]
                : []
            );
          }, 100);
        }
      } catch (err) {
        setError('Error processing graph data: ');
        console.error('Error processing graph data:', err);
        setLoading(false);
      }
    };

    return () => socket.close();
  }, []);

  // Helper function to animate link direction from target to source
  function animateLinkDirection(selection: any) {
    selection
      .attr('stroke-dasharray', '5,5') // dashed stroke
      .attr('stroke-dashoffset', 10) // initial offset
      .transition()
      .duration(1000)
      .ease(d3.easeLinear)
      .attr('stroke-dashoffset', 0) // animate offset to 0
      .on('end', function repeat(this: any) {
        d3.select(this)
          .attr('stroke-dashoffset', 10)
          .transition()
          .duration(1000)
          .ease(d3.easeLinear)
          .attr('stroke-dashoffset', 0)
          .on('end', repeat); // loop animation
      });
  }

  const animateCohorts = (firstCohort: string[], lastCohort: string[]) => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);

    // Animate first cohort nodes
    if (firstCohort.length > 0) {
      svg
        .selectAll('.node')
        .filter((d: any) => firstCohort.includes(d.id))
        .select('ellipse')
        .attr('stroke', '#FF8500')
        .attr('stroke-width', 3)
        .transition()
        .duration(1000)
        .attr('stroke-width', 2)
        .attr('stroke', '#fff');
    }

    // Animate last cohort nodes
    if (lastCohort.length > 0) {
      svg
        .selectAll('.node')
        .filter((d: any) => lastCohort.includes(d.id))
        .select('ellipse')
        .attr('stroke', '#FF8500')
        .attr('stroke-width', 3)
        .transition()
        .duration(1000)
        .attr('stroke-width', 2)
        .attr('stroke', '#fff');
    }

    if (firstCohort.length > 0) {
      const selectedLinks = svg
        .selectAll('.link')
        .filter(
          (d: any) =>
            firstCohort.includes(d.source) || firstCohort.includes(d.target)
        )
        .attr('stroke-width', 2)
        .attr('stroke', '#FF8500');

      animateLinkDirection(selectedLinks);
    }

    // Animate links connected to last cohort
    if (lastCohort.length > 0) {
      const selectedLinks = svg
        .selectAll('.link')
        .filter(
          (d: any) =>
            lastCohort.includes(d.source) || lastCohort.includes(d.target)
        )
        .attr('stroke-width', 2)
        .attr('stroke', '#FF8500');

      animateLinkDirection(selectedLinks);
    }
  };
  const handleResetZoom = () => {
    setDefaultZoom(0.3);
  };

  const handleZoomIn = () => {
    setDefaultZoom((prevZoom) => Math.min(prevZoom + 0.1, 5));
  };

  const handleZoomOut = () => {
    setDefaultZoom((prevZoom) => Math.max(prevZoom - 0.1, 0.3));
  };

  // have not used it YET.. might come in handy in the future
  const [_svgHeight, setSvgHeight] = useState(height);

  useEffect(() => {
    if (!svgRef.current || !graphData) return;
    const filteredCohorts = graphData.cohorts.slice(-selectedCohorts);
    const filteredCohortNodes = new Set(filteredCohorts.flat());

    const tooltip = d3
      .select(tooltipRef.current)
      .style('position', 'fixed')
      .style('visibility', 'hidden')
      .style('background', '#0077B6')
      .style('color', 'white')
      .style('border', '1px solid #FF8500')
      .style('border-radius', '5px')
      .style('padding', '10px')
      .style('box-shadow', '2px 2px 5px rgba(0,0,0,0.2)')
      .style('pointer-events', 'none')
      .style('z-index', '10')
      .style('bottom', '20px') // Position from bottom
      .style('right', '20px'); // Position from left

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const container = svg.append('g');

    zoomBehavior.current = d3
      .zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.5, 5])
      .on('zoom', (event: d3.D3ZoomEvent<SVGSVGElement, unknown>) => {
        container.attr('transform', event.transform.toString());
      });

    svg
      .call(zoomBehavior.current)
      .call(zoomBehavior.current.transform, d3.zoomIdentity.scale(defaultZoom));

    const allNodes = Object.keys(graphData.parents).map((id) => ({
      id,
      parents: graphData.parents[id],
      children: graphData.children[id],
    }));

    const hwPath = graphData.highest_work_path;
    const cohorts = graphData.cohorts;
    const positions = layoutNodes(allNodes, hwPath);
    const hwPathSet = new Set(hwPath);

    // Calculate required height based on node positions
    const allY = Object.values(positions).map((pos) => pos.y);
    // const minY = Math.min(...allY);
    // const maxY = Math.max(...allY);
    const padding = 100; // Additional padding
    const dynamicHeight = height / 2 + margin.top + margin.bottom + padding;
    setSvgHeight(dynamicHeight);

    // making old nodes invisible
    const visibleNodes = allNodes.filter((node) =>
      filteredCohortNodes.has(node.id)
    );
    let minVisibleX = Infinity;
    visibleNodes.forEach((node) => {
      const x = positions[node.id]?.x || 0;
      if (x < minVisibleX) minVisibleX = x;
    });
    const offsetX = margin.left - minVisibleX;

    const links: { source: string; target: string }[] = [];
    allNodes.forEach((node) => {
      if (Array.isArray(node.children)) {
        // Check if children exists and is an array
        node.children.forEach((childId) => {
          links.push({ target: node.id, source: childId });
        });
      }
    });

    const nodes = container
      .selectAll('.node')
      .data(allNodes)
      .enter()
      .append('g')
      .attr('class', 'node')
      .attr(
        'transform',
        (d) =>
          `translate(${(positions[d.id]?.x || 0) + offsetX},${positions[d.id]?.y || 0})`
      ) // Apply offset
      .style('display', (d) =>
        filteredCohortNodes.has(d.id) ? 'inline' : 'none'
      );

    const cohortMap = new Map<string, number>();
    (cohorts as string[][]).forEach((cohort, index) => {
      cohort.forEach((nodeId) => cohortMap.set(nodeId, index));
    });

    function getEllipseEdgePoint(
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
      const scale =
        1 / Math.sqrt((nx * nx) / (rx * rx) + (ny * ny) / (ry * ry));

      return {
        x: src.x + nx * scale,
        y: src.y + ny * scale,
      };
    }

    container
      .selectAll('.link')
      .data(links)
      .enter()
      .append('line')
      .attr('class', 'link')
      .attr('x1', (d) => {
        const src = {
          x: (positions[d.source]?.x || 0) + offsetX,
          y: positions[d.source]?.y || 0,
        };
        const tgt = {
          x: (positions[d.target]?.x || 0) + offsetX,
          y: positions[d.target]?.y || 0,
        };
        const point = getEllipseEdgePoint(
          src,
          tgt,
          nodeRadius + 10,
          nodeRadius
        ); // rx, ry
        return point.x;
      })
      .attr('y1', (d) => {
        const src = {
          x: (positions[d.source]?.x || 0) + offsetX,
          y: positions[d.source]?.y || 0,
        };
        const tgt = {
          x: (positions[d.target]?.x || 0) + offsetX,
          y: positions[d.target]?.y || 0,
        };
        const point = getEllipseEdgePoint(
          src,
          tgt,
          nodeRadius + 10,
          nodeRadius
        );
        return point.y;
      })
      .attr('x2', (d) => {
        const src = {
          x: (positions[d.source]?.x || 0) + offsetX,
          y: positions[d.source]?.y || 0,
        };
        const tgt = {
          x: (positions[d.target]?.x || 0) + offsetX,
          y: positions[d.target]?.y || 0,
        };
        const point = getEllipseEdgePoint(
          tgt,
          src,
          nodeRadius + 10,
          nodeRadius
        ); // reverse direction
        return point.x;
      })
      .attr('y2', (d) => {
        const src = {
          x: (positions[d.source]?.x || 0) + offsetX,
          y: positions[d.source]?.y || 0,
        };
        const tgt = {
          x: (positions[d.target]?.x || 0) + offsetX,
          y: positions[d.target]?.y || 0,
        };
        const point = getEllipseEdgePoint(
          tgt,
          src,
          nodeRadius + 10,
          nodeRadius
        );
        return point.y;
      })
      .attr('stroke', (d) =>
        hwPathSet.has(d.source) && hwPathSet.has(d.target)
          ? '#FF8500'
          : '#48CAE4'
      )
      .attr('stroke-width', 1.5)
      .attr('marker-end', (d) =>
        hwPathSet.has(d.source) && hwPathSet.has(d.target)
          ? 'url(#arrow-orange)'
          : 'url(#arrow-blue)'
      )
      .style('display', (d) =>
        filteredCohortNodes.has(d.source) && filteredCohortNodes.has(d.target)
          ? 'inline'
          : 'none'
      );

    nodes
      .each(function (d: GraphNode) {
        const nodeSelection = d3.select(this);
        nodeSelection.selectAll('ellipse, rect').remove(); // Remove existing shape

        // Conditional rendering: rectangle or ellipse
        if (
          d.id === latestBeadHashForHighlight &&
          filteredCohortNodes.has(d.id)
        ) {
          nodeSelection
            .append('rect')
            .attr('x', -(nodeRadius + 10)) // half width
            .attr('y', -nodeRadius) // half height
            .attr('width', (nodeRadius + 10) * 2)
            .attr('height', nodeRadius * 2)
            .attr('rx', 5) // rounded corners
            .attr('ry', 5)
            .attr('fill', 'red') // Red for the highlighted bead
            .attr('stroke', '#fff')
            .attr('stroke-width', 2);
        } else {
          nodeSelection
            .append('ellipse')
            .attr('rx', nodeRadius + 10) // horizontal radius
            .attr('ry', nodeRadius) // vertical radius
            .attr('r', nodeRadius)
            .attr('fill', () => {
              const cohortIndex = cohortMap.get(d.id);
              if (cohortIndex === undefined) return COLORS[0];
              return COLORS[cohortIndex % COLORS.length];
            })
            .attr('stroke', '#fff')
            .attr('stroke-width', 2);
        }
      })
      .on('mouseover', function (event: MouseEvent, d: GraphNode) {
        d3.select(this)
          .select('ellipse, rect')
          .attr('stroke', '#FF8500')
          .attr('stroke-width', 3);

        const cohortIndex = cohortMap.get(d.id);
        const isHWP = hwPathSet.has(d.id);

        const tooltipContent = `
                <div><strong>ID:</strong> ${nodeIdMap[d.id] || '?'} (${d.id})</div>
                <div><strong>Cohort:</strong> ${cohortIndex !== undefined ? cohortIndex : 'N/A'}</div>
                <div><strong>Highest Work Path:</strong> ${isHWP ? 'Yes' : 'No'}</div>
                <div><strong>Parents:</strong> ${
                  d.parents.length > 0
                    ? d.parents.map((p) => `${nodeIdMap[p] || '?'}`).join(', ')
                    : 'None'
                }
                `;

        tooltip.html(tooltipContent).style('visibility', 'visible');
      })
      .on('mouseout', function () {
        d3.select(this)
          .select('ellipse, rect')
          .attr('stroke', '#fff')
          .attr('stroke-width', 2);
        tooltip.style('visibility', 'hidden');
      });

    nodes
      .append('text')
      .attr('dy', 5)
      .attr('text-anchor', 'middle')
      .text((d) => `${d.id.slice(-4)}`)
      .attr('fill', '#fff')
      .style('font-size', 25)
      .on('mouseover', function (event: MouseEvent, d: GraphNode) {
        const cohortIndex = cohortMap.get(d.id);
        const isHWP = hwPathSet.has(d.id);
        const tooltipContent = `
                <div><strong>ID:</strong> ${nodeIdMap[d.id] || '?'} (${d.id})</div>
                <div><strong>Cohort:</strong> ${cohortIndex !== undefined ? cohortIndex : 'N/A'}</div>
                <div><strong>Highest Work Path:</strong> ${isHWP ? 'Yes' : 'No'}</div>
                <div><strong>Parents:</strong> ${
                  d.parents.length > 0
                    ? d.parents.map((p) => `${nodeIdMap[p] || '?'}`).join(', ')
                    : 'None'
                }
                  `;

        tooltip.html(tooltipContent).style('visibility', 'visible');
      })
      .on('mouseout', function () {
        tooltip.style('visibility', 'hidden');
      });
    container
      .append('text')
      .attr('x', width / 2)
      .attr('y', margin.top / 2)
      .attr('text-anchor', 'middle')
      .style('font-size', '16px');

    container
      .append('defs')
      .selectAll('marker')
      .data([
        { id: 'arrow-blue', color: '#48CAE4' },
        { id: 'arrow-orange', color: '#FF8500' },
      ])
      .enter()
      .append('marker')
      .attr('id', (d) => d.id)
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 10)
      .attr('refY', 0)
      .attr('markerWidth', 15)
      .attr('markerHeight', 12)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', (d) => d.color);
  }, [
    graphData,
    defaultZoom,
    selectedCohorts,
    graphUpdateCounter,
    latestBeadHashForHighlight,
  ]);

  if (loading) {
    return (
      <div className="flex items-center justify-center h-full w-full">
        <div className="flex flex-col items-center">
          <Loader className="h-8 w-8 text-[#0077B6] animate-spin" />
          <p className="mt-4 text-[#0077B6]">Loading graph data...</p>
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="flex flex-col items-center justify-center h-screen">
        <div className="text-red-500 mb-4">Error: {error}</div>
        <button
          onClick={() => window.location.reload()}
          className="bg-[#0077B6] text-white px-4 py-2 rounded hover:bg-[#005691] transition-colors"
        >
          Retry
        </button>
      </div>
    );
  }

  if (!graphData) {
    return (
      <div className="flex flex-col items-center justify-center h-screen">
        <div className="text-[#0077B6] mb-4">No graph data available</div>
        <button
          onClick={() => window.location.reload()}
          className="bg-[#0077B6] text-white px-4 py-2 rounded hover:bg-[#005691] transition-colors"
        >
          Refresh
        </button>
      </div>
    );
  }

  return (
    <div className="min-h-screen p-2 bg-gray">
      <div className="m-2 relative flex gap-2 items-center">
        <select
          value={selectedCohorts}
          onChange={(e) => {
            const value = e.target.value;
            setSelectedCohorts(value === 'all' ? 'all' : Number(value));
          }}
          className="px-2 py-1 rounded border border-[#0077B6] bg-gray text-[#0077B6]"
        >
          <option value="all">Show all cohorts</option>
          {[1, 2, 3, 4, 5].map((value) => (
            <option key={value} value={value}>
              Show latest {value} cohorts
            </option>
          ))}
        </select>

        <div className="flex gap-1 ml-auto">
          <button
            onClick={handleZoomIn}
            className="bg-[#0077B6] text-white px-3 py-1 rounded hover:bg-[#005691] transition-colors min-w-[30px]"
          >
            +
          </button>
          <button
            onClick={handleZoomOut}
            className="bg-[#0077B6] text-white px-3 py-1 rounded hover:bg-[#005691] transition-colors min-w-[30px]"
          >
            -
          </button>
          <button
            onClick={handleResetZoom}
            className="bg-[#0077B6] text-white px-3 py-1 rounded hover:bg-[#005691] transition-colors"
          >
            Reset Zoom
          </button>
        </div>
      </div>

      <div className="m-2 relative">
        <div className="border border-[#FF8500] rounded-lg bg-gray shadow-lg">
          <svg ref={svgRef} width={width} height={height} />
          <div
            ref={tooltipRef}
            className="fixed bg-[#0077B6] text-white border border-[#FF8500] rounded p-2 shadow-lg pointer-events-none z-10 bottom-5 right-5"
          ></div>
        </div>
      </div>

      <div className="m-2 border border-[#0077B6] rounded-lg bg-gray shadow-lg p-4">
        <h3 className="text-xl font-semibold text-[#FF8500] mb-4">Metrics</h3>
        <div className="flex flex-col gap-2">
          <div className="font-medium text-[#0077B6]">
            Total Beads:{' '}
            <span className="font-normal text-[#FF8500]">{totalBeads}</span>
          </div>
          <div className="font-medium text-[#0077B6]">
            Total Cohorts:{' '}
            <span className="font-normal text-[#FF8500]">{totalCohorts}</span>
          </div>
          <div className="font-medium text-[#0077B6]">
            Max Cohort Size:{' '}
            <span className="font-normal text-[#FF8500]">{maxCohortSize}</span>
          </div>
          <div className="font-medium text-[#0077B6]">
            HWP Length:{' '}
            <span className="font-normal text-[#FF8500]">{hwpLength}</span>
          </div>
        </div>
      </div>
    </div>
  );
};

export default GraphVisualization;
