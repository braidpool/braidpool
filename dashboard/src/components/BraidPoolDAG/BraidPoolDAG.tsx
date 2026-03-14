import React, { useRef, useEffect, useState } from 'react';
import * as d3 from 'd3';
import { Loader } from 'lucide-react';
import { GraphData, GraphNode, NodeIdMapping, BeadRecord } from './Types';
import {
  layoutNodes,
  getEllipseEdgePoint,
  animateLinkDirection,
} from './BraidPoolDAGUtils';
import { WEBSOCKET_URLS } from '../../URLs';
import {
  NODE_RADIUS,
  PADDING,
  COLORS,
  COLUMN_WIDTH,
  VERTICAL_SPACING,
} from './Constants';
import { ChevronDown, ChevronUp } from 'lucide-react';

const GraphVisualization: React.FC = () => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [graphData, setGraphData] = useState<GraphData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [isPlaying, setIsPlaying] = useState(true);
  const isPlayingRef = useRef(true);
  const width = window.innerWidth - 100;
  const margin = { top: 0, right: 0, bottom: 0, left: 50 };
  const [svgHeight, setSvgHeight] = useState(600);
  const [nodeIdMap, setNodeIdMap] = useState<NodeIdMapping>({});
  const [selectedCohorts, setSelectedCohorts] = useState<number | 'all'>(5);
  const nodeRadius = NODE_RADIUS;
  const tooltipRef = useRef<HTMLDivElement>(null);

  const [graphUpdateCounter, setGraphUpdateCounter] = useState(0);
  const [latestBeadHashForHighlight, setLatestBeadHashForHighlight] = useState<
    string | null
  >(null);

  const prevFirstCohortRef = useRef<string[]>([]);
  const prevLastCohortRef = useRef<string[]>([]);
  const [_connectionStatus, setConnectionStatus] = useState('Disconnected');

  const [totalBeads, setTotalBeads] = useState<number>(0);
  const [totalCohorts, setTotalCohorts] = useState<number>(0);
  const [maxCohortSize, setMaxCohortSize] = useState<number>(0);
  const [hwpLength, setHwpLength] = useState<number>(0);

  const [defaultZoom, setDefaultZoom] = useState(0.3);
  const zoomBehavior = useRef<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(
    null
  );
  const zoomTransformRef = useRef<d3.ZoomTransform | null>(null);

  const [consecutiveZoomInCount, setConsecutiveZoomInCount] = useState(0);
  const [consecutiveZoomOutCount, setConsecutiveZoomOutCount] = useState(0);

  const [beadRecords, setBeadRecords] = useState<BeadRecord[]>([]);
  const [maxBeadRecords] = useState(7);
  const [expandedRows, setExpandedRows] = useState<Set<string>>(new Set());
  const toggleRowExpansion = (hash: string) => {
    setExpandedRows((prev) => {
      const newSet = new Set(prev);
      if (newSet.has(hash)) {
        newSet.delete(hash);
      } else {
        newSet.add(hash);
      }
      return newSet;
    });
  };

  useEffect(() => {
    isPlayingRef.current = isPlaying;
  }, [isPlaying]);

  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      const target = event.target as HTMLElement | null;
      if (
        target &&
        (target.tagName === 'INPUT' ||
          target.tagName === 'TEXTAREA' ||
          target.tagName === 'SELECT' ||
          target.isContentEditable)
      ) {
        return;
      }

      if (event.key === ' ' || event.key === 'p' || event.key === 'P') {
        event.preventDefault();
        setIsPlaying((prev) => !prev);
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, []);

  useEffect(() => {
    const url = WEBSOCKET_URLS.BRAIDPOOL_DAG_WEBSOCKET;
    const socket = new WebSocket(url);
    let isMounted = true;

    socket.onopen = () => {
      if (!isMounted) return;
      console.log('Connected to WebSocket', url);
      setConnectionStatus('Connected');
    };

    socket.onclose = () => {
      if (!isMounted) return;
      setConnectionStatus('Disconnected');
    };

    socket.onerror = (err) => {
      if (!isMounted) return;
      setConnectionStatus(`Error: ${err}`);
    };

    socket.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const parsed = JSON.parse(event.data);
        const parsedData = parsed.data;
        console.log('Received data:', parsedData);
        if (!isPlayingRef.current) {
          return;
        }
        if (!parsedData?.parents || typeof parsedData.parents !== 'object') {
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

        // Track new beads for the table
        const hwPathSet = new Set(parsedData.highest_work_path);
        const newBeads: BeadRecord[] = [];

        if (lastCohortChanged && parsedData?.cohorts?.length > 0) {
          const lastCohort = parsedData.cohorts[parsedData.cohorts.length - 1];
          lastCohort.forEach((beadHash: string) => {
            const parents = parsedData.parents[beadHash] || [];
            const childrenList = children[beadHash] || [];
            const cohortIndex = parsedData.cohorts.findIndex((c: string[]) =>
              c.includes(beadHash)
            );

            newBeads.push({
              hash: beadHash,
              parentHashes: parents,
              parentCount: parents.length,
              childHashes: childrenList,
              childCount: childrenList.length,
              isHWP: hwPathSet.has(beadHash),
              timestamp: new Date().toLocaleTimeString(),
              cohortIndex: cohortIndex,
            });
          });

          if (newBeads.length > 0) {
            setBeadRecords((prev) => {
              const updated = [...newBeads, ...prev];
              return updated.slice(0, maxBeadRecords);
            });
          }
        }

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
          if (!isPlayingRef.current) {
            return;
          }
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

    return () => {
      isMounted = false;
      if (socket.readyState === WebSocket.OPEN) {
        socket.close();
      }
    };
  }, []);

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

  const buildZoomTransform = (nextZoom: number) => {
    const currentTransform = zoomTransformRef.current;
    const currentX = currentTransform ? currentTransform.x : 0;
    const currentY = currentTransform ? currentTransform.y : 0;
    return d3.zoomIdentity.translate(currentX, currentY).scale(nextZoom);
  };

  const handleResetZoom = () => {
    const nextZoom = 0.3;
    setDefaultZoom(nextZoom);
    zoomTransformRef.current = buildZoomTransform(nextZoom);

    setConsecutiveZoomInCount(0);
    setConsecutiveZoomOutCount(0);
  };

  const handleZoomIn = () => {
    if (consecutiveZoomInCount >= 3) {
      return;
    }

    setDefaultZoom((prevZoom) => {
      const nextZoom = prevZoom + 0.1;
      zoomTransformRef.current = buildZoomTransform(nextZoom);
      return nextZoom;
    });
    setConsecutiveZoomInCount((prev) => prev + 1);
    setConsecutiveZoomOutCount(0);
  };

  const handleZoomOut = () => {
    if (consecutiveZoomOutCount >= 3) {
      return;
    }

    setDefaultZoom((prevZoom) => {
      const nextZoom = Math.max(prevZoom - 0.1, 0.1);
      zoomTransformRef.current = buildZoomTransform(nextZoom);
      return nextZoom;
    });
    setConsecutiveZoomOutCount((prev) => prev + 1);
    setConsecutiveZoomInCount(0);
  };

  useEffect(() => {
    if (!svgRef.current || !graphData) return;
    const filteredCohorts = graphData.cohorts.slice(-selectedCohorts);
    const filteredCohortNodes = new Set(filteredCohorts.flat());

    const tooltip = d3.select(tooltipRef.current).style('visibility', 'hidden');

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const container = svg.append('g');

    zoomBehavior.current = d3
      .zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.5, 5])
      .on('zoom', (event: d3.D3ZoomEvent<SVGSVGElement, unknown>) => {
        container.attr('transform', event.transform.toString());
        zoomTransformRef.current = event.transform;
      });

    svg
      .call(zoomBehavior.current)
      .call(
        zoomBehavior.current.transform,
        zoomTransformRef.current ??
          d3.zoomIdentity.translate(0, 50).scale(defaultZoom)
      );

    const allNodes = Object.keys(graphData.parents).map((id) => ({
      id,
      parents: graphData.parents[id],
      children: graphData.children[id],
    }));

    const hwPath = graphData.highest_work_path;
    const cohorts = graphData.cohorts;
    const positions = layoutNodes(
      allNodes,
      hwPath,
      {},
      {},
      width,
      margin,
      COLUMN_WIDTH,
      VERTICAL_SPACING
    );
    const hwPathSet = new Set(hwPath);

    // Calculate required height based on node positions
    const allY = Object.values(positions).map((pos) => pos.y);
    const minY = Math.min(...allY);
    const maxY = Math.max(...allY);
    const padding = PADDING * 2; // Additional padding top and bottom
    const dynamicHeight = maxY - minY + padding;
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
      .attr('stroke-width', 1)
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
      .style('font-size', 40)
      .style('font-weight', 'bold')
      .on('mouseover', function (event: MouseEvent, d: GraphNode) {
        const cohortIndex = cohortMap.get(d.id);
        const isHWP = hwPathSet.has(d.id);
        const hwpPosition = isHWP ? hwPath.indexOf(d.id) + 1 : null;

        const tooltipContent = `
                <div style="max-width: 400px; font-size: 12px; line-height: 1.6;">
                  <div style="margin-bottom: 8px; padding-bottom: 8px;">
                    <strong >Bead Information</strong>
                  </div>
                  
                  <div style="margin-bottom: 4px; word-break: break-all;"><strong> Hash:</strong> <span style="font-family: monospace; font-size: 10px;">${d.id}</span></div>
                  <div style="margin-bottom: 4px;"><strong>Cohort Index:</strong> ${cohortIndex !== undefined ? cohortIndex : 'N/A'}</div>
                  <div style="margin-bottom: 4px;"><strong>On HWP:</strong> <span style="color: ${isHWP ? '#4ade80' : '#ef4444'};">${isHWP ? 'Yes' : 'No'}${hwpPosition ? ` (Position: ${hwpPosition})` : ''}</span></div>
                  
                  <div style="margin-top: 8px; padding-top: 8px; border-top: 1px solid #48CAE4;">
                    <strong>Parents (${d.parents.length}):</strong>
                    ${
                      d.parents.length > 0
                        ? `
                      <div style="margin-top: 4px; padding-left: 8px;">
                        ${d.parents
                          .map(
                            (p) => `
                          <div style="margin: 2px 0; font-size: 10px;">
                            <span style="color: #FF8500;">→
                            <span style="font-family: monospace; color: #48CAE4;">${p.slice(0, 12)}...${p.slice(-8)}</span>
                          </div>
                        `
                          )
                          .join('')}
                      </div>
                    `
                        : '<span style="color: #999;"> None (Genesis)</span>'
                    }
                  </div>
                  
                  <div style="margin-top: 8px; padding-top: 8px; border-top: 1px solid #48CAE4;">
                    <strong>Children (${d.children?.length || 0}):</strong>
                    ${
                      d.children && d.children.length > 0
                        ? `
                      <div style="margin-top: 4px; padding-left: 8px;">
                        ${d.children
                          .slice(0, 5)
                          .map(
                            (c) => `
                          <div style="margin: 2px 0; font-size: 10px;">
                            <span style="color: #4ade80;">→</span> 
                            <span style="font-family: monospace; color: #48CAE4;">${c.slice(0, 12)}...${c.slice(-8)}</span>
                          </div>
                        `
                          )
                          .join('')}
                        ${d.children.length > 5 ? `<div style="margin-top: 2px; color: #999; font-size: 10px;">... and ${d.children.length - 5} more</div>` : ''}
                      </div>
                    `
                        : '<span style="color: #999;"> None (Leaf bead)</span>'
                    }
                  </div>
                </div>
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
    <div>
      <div>
        <div className=" h-[650px] border border-gray-600 backdrop-blur-2xl  rounded-lg  shadow-lg overflow-hidden mt-2">
          <div className="m-2 relative flex gap-2 items-center">
            <select
              value={selectedCohorts}
              onChange={(e) => {
                const value = e.target.value;
                setSelectedCohorts(value === 'all' ? 'all' : Number(value));
              }}
              className="px-2 py-1 rounded border border-[#0077B6]  text-[#0077B6]"
            >
              <option value="all">Show all cohorts</option>
              {[1, 2, 3, 4, 5].map((value) => (
                <option key={value} value={value}>
                  Show latest {value} cohorts
                </option>
              ))}
            </select>
            <div className="m-2 flex items-center justify-between shadow-lg p-4 ml-[150px]">
              <div className="flex gap-6 ">
                <div className="font-medium text-[#0077B6]">
                  Total Beads:{' '}
                  <span className="font-normal text-[#FF8500]">
                    {totalBeads}
                  </span>
                </div>
                <div className="font-medium text-[#0077B6]">
                  Total Cohorts:{' '}
                  <span className="font-normal text-[#FF8500]">
                    {totalCohorts}
                  </span>
                </div>
                <div className="font-medium text-[#0077B6]">
                  Max Cohort Size:{' '}
                  <span className="font-normal text-[#FF8500]">
                    {maxCohortSize}
                  </span>
                </div>
                <div className="font-medium text-[#0077B6]">
                  HWP Length:{' '}
                  <span className="font-normal text-[#FF8500]">
                    {hwpLength}
                  </span>
                </div>
              </div>
            </div>
            <div className="flex gap-1 ml-auto">
              <button
                onClick={handleZoomIn}
                disabled={consecutiveZoomInCount >= 3}
                className={`px-3 py-1 rounded transition-colors min-w-[30px] ${
                  consecutiveZoomInCount >= 3
                    ? 'bg-gray-400 text-gray-600 cursor-not-allowed'
                    : 'bg-[#0077B6] text-white hover:bg-[#005691]'
                }`}
                title={
                  consecutiveZoomInCount >= 3
                    ? 'Zoom out to enable zoom in'
                    : 'Zoom in'
                }
              >
                +
              </button>
              <button
                onClick={handleZoomOut}
                disabled={consecutiveZoomOutCount >= 3}
                className={`px-3 py-1 rounded transition-colors min-w-[30px] ${
                  consecutiveZoomOutCount >= 3
                    ? 'bg-gray-400 text-gray-600 cursor-not-allowed'
                    : 'bg-[#0077B6] text-white hover:bg-[#005691]'
                }`}
                title={
                  consecutiveZoomOutCount >= 3
                    ? 'Zoom in to enable zoom out'
                    : 'Zoom out'
                }
              >
                -
              </button>
              <button
                onClick={handleResetZoom}
                className="bg-[#0077B6] text-white px-3 py-1 rounded hover:bg-[#005691] transition-colors"
              >
                Reset Zoom
              </button>
              <button
                onClick={() => setIsPlaying((prev) => !prev)}
                className="bg-[#0077B6] text-white px-3 py-1 rounded hover:bg-[#005691] transition-colors"
              >
                {isPlaying ? 'Pause' : 'Resume'}
              </button>
            </div>
          </div>
          <svg
            ref={svgRef}
            width={width}
            height={svgHeight}
            className="block"
          />
          <div
            ref={tooltipRef}
            className="fixed  text-white border  rounded p-2 shadow-lg pointer-events-none z-10 bottom-5 right-5 mb-[200px]  border-gray-600 backdrop-blur-lg  "
          ></div>
        </div>
      </div>
      <div></div>
      {/*  Beads Table */}
      <div className="m-2 border border-gray-600 backdrop-blur-2xl  rounded-lg  shadow-lg ">
        <div className="p-4 ">
          <h3 className="text-xl font-semibold text-white">
            Incoming Beads ({beadRecords.length})
          </h3>
        </div>
        <div
          className="overflow-x-auto"
          style={{ maxHeight: '700px', overflowY: 'auto' }}
        >
          <table className="w-full text-sm">
            <thead className=" text-white ">
              <tr>
                <th className="px-3 py-2 text-left font-semibold w-12"></th>
                <th className="px-3 py-2 text-left font-semibold">Bead Hash</th>
                <th className="px-3 py-2 text-center font-semibold">
                  Timestamp
                </th>
                <th className="px-3 py-2 text-center font-semibold">
                  Cohort Index
                </th>
                <th className="px-3 py-2 text-center font-semibold">Parents</th>
                <th className="px-3 py-2 text-center font-semibold">
                  Children
                </th>
                <th className="px-3 py-2 text-center font-semibold">HWP</th>
              </tr>
            </thead>
            <tbody>
              {beadRecords.length === 0 ? (
                <tr>
                  <td colSpan={7} className="px-3 py-8 text-center ">
                    Waiting for new beads...
                  </td>
                </tr>
              ) : (
                beadRecords.map((bead, index) => (
                  <React.Fragment key={`${bead.hash}-${index}`}>
                    <tr
                      className={`border-t  border-gray-700 hover:bg-opacity-10 cursor-pointer transition-colors ${
                        index === 0 ? ' bg-opacity-5' : ''
                      }`}
                      onClick={() => toggleRowExpansion(bead.hash)}
                    >
                      <td className="px-3 py-3 text-center">
                        <span className="text-[#0077B6] text-lg">
                          {expandedRows.has(bead.hash) ? (
                            <ChevronUp className="h-5 w-5 text-blue-400" />
                          ) : (
                            <ChevronDown className="h-5 w-5 text-white" />
                          )}
                        </span>
                      </td>
                      <td className="px-3 py-3">
                        <div className="flex items-center gap-2">
                          <span
                            className="font-mono text-xs "
                            title={bead.hash}
                          >
                            {bead.hash.slice(0, 16)}...{bead.hash.slice(-8)}
                          </span>
                        </div>
                      </td>
                      <td className="px-3 py-3 text-center text-xs">
                        {bead.timestamp}
                      </td>
                      <td className="px-3 py-3 text-center">
                        <span className="inline-block px-2 py-1  bg-opacity-20  rounded text-xs font-semibold">
                          {(() => {
                            const currentIndex = graphData?.cohorts.findIndex(
                              (c: string[]) => c.includes(bead.hash)
                            );
                            return currentIndex !== undefined &&
                              currentIndex !== -1
                              ? currentIndex
                              : 'N/A';
                          })()}
                        </span>
                      </td>
                      <td className="px-3 py-3 text-center">
                        <span className="inline-block px-2 py-1  bg-opacity-20  rounded text-xs font-bold">
                          {bead.parentCount}
                        </span>
                      </td>
                      <td className="px-3 py-3 text-center">
                        <span className="inline-block px-2 py-1  rounded text-xs font-bold">
                          {bead.childCount}
                        </span>
                      </td>
                      <td className="px-3 py-3 text-center">
                        {bead.isHWP ? (
                          <span className="inline-block px-3 py-1  text-white rounded text-xs font-semibold shadow">
                            YES
                          </span>
                        ) : (
                          <span className="inline-block px-3 py-1  text-white rounded text-xs">
                            NO
                          </span>
                        )}
                      </td>
                    </tr>

                    {/* Parents  & Children Section  */}
                    {expandedRows.has(bead.hash) && (
                      <tr className="bg-opacity-5 border-t border-[#48CAE4]">
                        <td></td>
                        <td colSpan={6} className="px-4 py-4">
                          <div className="space-y-3">
                            <div className="flex items-start gap-2">
                              <span className="font-semibold text-[#0077B6] min-w-[80px]">
                                Parents:
                              </span>
                              {bead.parentCount === 0 ? (
                                <span className="text-gray-500 italic">
                                  None (Genesis Bead)
                                </span>
                              ) : (
                                <div className="flex-1 space-y-1">
                                  {bead.parentHashes.map((ph, idx) => (
                                    <div
                                      key={idx}
                                      className="font-mono text-xs text-white flex items-center gap-2"
                                      title={ph}
                                    >
                                      <span>
                                        {ph.slice(0, 16)}...{ph.slice(-12)}
                                      </span>
                                    </div>
                                  ))}
                                </div>
                              )}
                            </div>
                            <div className="flex items-start gap-2">
                              <span className="font-semibold text-[#0077B6] min-w-[80px]">
                                Children:
                              </span>
                              {bead.childCount === 0 ? (
                                <span className="text-gray-500 italic">
                                  None (Leaf Bead)
                                </span>
                              ) : (
                                <div className="flex-1 space-y-1">
                                  {bead.childHashes
                                    .slice(0, 5)
                                    .map((ch, idx) => (
                                      <div
                                        key={idx}
                                        className="font-mono text-xs text-[#48CAE4] flex items-center gap-2"
                                        title={ch}
                                      >
                                        <span>
                                          {ch.slice(0, 16)}...{ch.slice(-12)}
                                        </span>
                                      </div>
                                    ))}
                                  {bead.childCount > 5 && (
                                    <div className="text-white italic text-xs pl-6">
                                      ... and {bead.childCount - 5} more
                                      children
                                    </div>
                                  )}
                                </div>
                              )}
                            </div>
                          </div>
                        </td>
                      </tr>
                    )}
                  </React.Fragment>
                ))
              )}
            </tbody>
          </table>
        </div>
      </div>
    </div>
  );
};

export default GraphVisualization;
