import React, { useRef, useEffect, useState } from 'react';
import * as d3 from 'd3';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import CardHeader from '@mui/material/CardHeader';
import CardTitle from '@mui/material/Typography';
import '../../App.css';
import Button from '@mui/material/Button';
import { CircularProgress } from '@mui/material';
import { layout } from './braid';

interface GraphNode {
  id: string;
  parents: string[];
  children: string[];
}

interface NodeIdMapping {
  [hash: string]: string; // maps hash to sequential ID
}

var COLORS = [
  `rgba(${217}, ${95}, ${2}, 1)`,
  `rgba(${117}, ${112}, ${179}, 1)`,
  `rgba(${102}, ${166}, ${30}, 1)`,
  `rgba(${231}, ${41}, ${138}, 1)`,
];
interface GraphData {
  highest_work_path: string[];
  parents: Record<string, string[]>;
  children: Record<string, string[]>;
  cohorts: string[][];
  bead_count: number;
}

interface Position {
  x: number;
  y: number;
}

const GraphVisualization: React.FC = () => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [graphData, setGraphData] = useState<GraphData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const width = window.innerWidth - 100;
  const height = window.innerHeight;

  const [nodeIdMap, setNodeIdMap] = useState<NodeIdMapping>({});
  const [selectedCohorts, setSelectedCohorts] = useState<number | 'all'>(10);

  const nodeRadius = 30;
  const margin = { top: 0, right: 0, bottom: 0, left: 50 };
  const tooltipRef = useRef<HTMLDivElement>(null);

  const COLUMN_WIDTH = 120;
  const VERTICAL_SPACING = 100;

  // Utility functions to convert between data structures
  function objectToMap(
    obj: Record<string, string[]>
  ): Map<string, Set<string>> {
    const map = new Map();
    Object.entries(obj).forEach(([key, values]) => {
      map.set(key, new Set(values));
    });
    return map;
  }
  const cohortCache = useRef<Map<number, [number, number]>[]>([]);
  const MAX_CACHED_COHORTS = 10;

  const layoutNodes = (
    allNodes: GraphNode[],
    hwPath: string[],
    cohorts: string[][]
  ): Record<string, Position> => {
    const allParents = objectToMap(graphData?.parents || {});
    const allChildren = objectToMap(graphData?.children || {});
    const positions: Record<string, Position> = {};
    let previousTipsPos: Map<string, [number, number]> | null = null;

    // Process each cohort sequentially
    for (const cohort of cohorts) {
      const cohortSet = new Set(cohort);
      const [cohortPositions] = layout(
        new Set(
          Array.from(cohortSet).map((id) => parseInt(nodeIdMap[id] || '0', 10))
        ),
        new Map(
          Array.from(allParents.entries()).map(([key, value]) => [
            parseInt(key, 10),
            new Set(Array.from(value).map((v) => parseInt(v, 10))),
          ])
        ),
        undefined, // beadWork (undefined for default)
        previousTipsPos
          ? new Map(
            Array.from(previousTipsPos.entries()).map(([key, value]) => [
              parseInt(key, 10),
              value,
            ])
          )
          : undefined
      );

      // Cache positions before scaling
      cohortCache.current.push(new Map(cohortPositions));
      if (cohortCache.current.length > MAX_CACHED_COHORTS) {
        cohortCache.current.shift();
      }

      // Convert and scale positions (-1 to 1 => -100 to 100)
      cohortPositions.forEach(([x, y], beadId) => {
        positions[beadId] = {
          // increasing or decreasing this is having no effect on the Ui somehow?
          x: x * 100,
          y: y * 100
        };
      });

      // Update previous tips for next cohort
      previousTipsPos = new Map();
      cohortPositions.forEach((pos, beadId) => {
        if (!allChildren.get(beadId.toString())?.size) {
          // If no children, it's a tip
          if (previousTipsPos) {
            previousTipsPos.set(beadId.toString(), pos);
          }
        }
      });
    }

    // Adjust positions to center the visualization
    const minX = Math.min(...Object.values(positions).map((p) => p.x));
    const minY = Math.min(...Object.values(positions).map((p) => p.y));
    const maxY = Math.max(...Object.values(positions).map((p) => p.y));

    const centerY = height / 2;
    const yOffset = centerY - (maxY + minY) / 2;

    // Apply offsets
    Object.keys(positions).forEach((beadId) => {
      positions[beadId].x += margin.left - minX;
      positions[beadId].y += yOffset;
    });

    // Calculate scaling and transformation
    const allCoords = Object.values(positions);
    const xExtent = d3.extent(allCoords, d => d.x) as [number, number];
    const yExtent = d3.extent(allCoords, d => d.y) as [number, number];

    const xScale = d3.scaleLinear()
      .domain(xExtent)
      .range([margin.left, width - margin.right]);

    const yScale = d3.scaleLinear()
      .domain(yExtent)
      .range([margin.top, height - margin.bottom]);

    // Center HWP nodes vertically --- this also does not work like the original code
    const hwPathSet = new Set(hwPath);
    const hwpNodes = Object.keys(positions).filter(id => hwPathSet.has(id));
    const hwpYValues = hwpNodes.map(id => positions[id].y);
    const hwpCenterY = hwpYValues.length > 0 ?
      d3.mean(hwpYValues) || height / 2 :
      height / 2;
    // Apply final positions with HWP centering
    Object.keys(positions).forEach(beadId => {
      const isHWP = hwPathSet.has(beadId);
      positions[beadId] = {
        x: xScale(positions[beadId].x),
        y: isHWP ? height / 2 : yScale(positions[beadId].y)
      };
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

  const animateCohorts = (firstCohort: string[], lastCohort: string[]) => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);

    // Animate first cohort nodes
    if (firstCohort.length > 0) {
      svg
        .selectAll('.node')
        .filter((d: any) => firstCohort.includes(d.id))
        .select('circle')
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
        .select('circle')
        .attr('stroke', '#FF8500')
        .attr('stroke-width', 3)
        .transition()
        .duration(1000)
        .attr('stroke-width', 2)
        .attr('stroke', '#fff');
    }

    // Animate links connected to first cohort
    if (firstCohort.length > 0) {
      svg
        .selectAll('.link')
        .filter(
          (d: any) =>
            firstCohort.includes(d.source) || firstCohort.includes(d.target)
        )
        .attr('stroke-width', 3)
        .attr('stroke', '#FF8500')
        .transition()
        .duration(1000)
        .attr('stroke-width', 1.5)
        .attr('stroke', (d: any) =>
          graphData?.highest_work_path.includes(d.source) &&
            graphData?.highest_work_path.includes(d.target)
            ? '#FF8500'
            : '#48CAE4'
        );
    }

    // Animate links connected to last cohort
    if (lastCohort.length > 0) {
      svg
        .selectAll('.link')
        .filter(
          (d: any) =>
            lastCohort.includes(d.source) || lastCohort.includes(d.target)
        )
        .attr('stroke-width', 3)
        .attr('stroke', '#FF8500')
        .transition()
        .duration(1000)
        .attr('stroke-width', 1.5)
        .attr('stroke', (d: any) =>
          graphData?.highest_work_path.includes(d.source) &&
            graphData?.highest_work_path.includes(d.target)
            ? '#FF8500'
            : '#48CAE4'
        );
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
      .style('bottom', '20px')
      .style('right', '20px');
  
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
    const positions = layoutNodes(allNodes, hwPath, cohorts as string[][]);
    const hwPathSet = new Set(hwPath);
  
    // Draw inter-cohort links using cache ---- this is not working as expected
    const drawInterCohortLinks = () => {
      const currentCohort = new Set(graphData.cohorts.flat());
      
      cohortCache.current.slice(0, -1).forEach(cachedCohort => {
        Array.from(cachedCohort.keys()).forEach(sourceId => {
          const targetIds = graphData.children[sourceId] || [];
          targetIds.filter(id => currentCohort.has(id)).forEach(targetId => {
            if (filteredCohortNodes.has(sourceId.toString()) && filteredCohortNodes.has(targetId)) {
              container.append('line')
                .attr('class', 'inter-cohort-link')
                .attr('x1', positions[sourceId]?.x || 0)
                .attr('y1', positions[sourceId]?.y || 0)
                .attr('x2', positions[targetId]?.x || 0)
                .attr('y2', positions[targetId]?.y || 0)
                .attr('stroke', '#888')
                .attr('stroke-width', 1)
                .attr('stroke-dasharray', '5,5')
                .attr('marker-end', 'url(#arrow-blue)');
            }
          });
        });
      });
    };
  
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
        node.children.forEach((childId) => {
          links.push({ target: node.id, source: childId });
        });
      }
    });
  
    // Draw inter-cohort links
    drawInterCohortLinks();
  
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
      )
      .style('display', (d) =>
        filteredCohortNodes.has(d.id) ? 'inline' : 'none'
      );
  
    const cohortMap = new Map<string, number>();
    (cohorts as string[][]).forEach((cohort, index) => {
      cohort.forEach((nodeId) => cohortMap.set(nodeId, index));
    });
  
    nodes
      .append('circle')
      .attr('r', nodeRadius)
      .attr('fill', (d) => {
        const cohortIndex = cohortMap.get(d.id);
        if (cohortIndex === undefined) return COLORS[0];
        return COLORS[cohortIndex % COLORS.length];
      })
      .attr('stroke', '#fff')
      .attr('stroke-width', 2)
      .on('mouseover', function (event: MouseEvent, d: GraphNode) {
        d3.select(this).attr('stroke', '#FF8500').attr('stroke-width', 3);
  
        const cohortIndex = cohortMap.get(d.id);
        const isHWP = hwPathSet.has(d.id);
  
        const tooltipContent = `
                <div><strong>ID:</strong> ${nodeIdMap[d.id] || '?'} (${d.id})</div>
                <div><strong>Cohort:</strong> ${cohortIndex !== undefined ? cohortIndex : 'N/A'}</div>
                <div><strong>Highest Work Path:</strong> ${isHWP ? 'Yes' : 'No'}</div>
                <div><strong>Parents:</strong> ${d.parents.length > 0
            ? d.parents.map((p) => `${nodeIdMap[p] || '?'}`).join(', ')
            : 'None'
          }</div>
                <div><strong>Children:</strong> ${d.children.length > 0
            ? d.children.map((c) => `${nodeIdMap[c] || '?'}`).join(', ')
            : 'None'
          }</div>
                `;
  
        tooltip.html(tooltipContent).style('visibility', 'visible');
      })
      .on('mouseout', function () {
        d3.select(this).attr('stroke', '#fff').attr('stroke-width', 2);
        tooltip.style('visibility', 'hidden');
      });
  
    nodes
      .append('text')
      .attr('dy', 4)
      .attr('text-anchor', 'middle')
      .text((d) => nodeIdMap[d.id] || '?')
      .attr('fill', '#fff')
      .style('font-size', 20);
  
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
        const dx = tgt.x - src.x;
        const dy = tgt.y - src.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist === 0) return src.x;
        const ratio = nodeRadius / dist;
        return src.x + dx * ratio;
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
        const dx = tgt.x - src.x;
        const dy = tgt.y - src.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist === 0) return src.y;
        const ratio = nodeRadius / dist;
        return src.y + dy * ratio;
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
        const dx = src.x - tgt.x;
        const dy = src.y - tgt.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist === 0) return tgt.x;
        const ratio = nodeRadius / dist;
        return tgt.x + dx * ratio;
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
        const dx = src.x - tgt.x;
        const dy = src.y - tgt.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist === 0) return tgt.y;
        const ratio = nodeRadius / dist;
        return tgt.y + dy * ratio;
      })
      .attr('stroke', (d) =>
        hwPathSet.has(d.source) && hwPathSet.has(d.target) ? '#FF8500' : '#48CAE4'
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
  }, [graphData, defaultZoom, selectedCohorts]);
  if (loading) {
    return (
      <div className="flex items-center justify-center h-full w-full">
        <div className="flex flex-col items-center">
          <CircularProgress className="h-8 w-8 animate-spin text-[#FF8500]" />
          <p className="mt-4 text-[#0077B6]">Loading graph data...</p>
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="flex flex-col items-center justify-center h-screen">
        <div className="text-red-500 mb-4">Error: {error}</div>
        <Button onClick={() => window.location.reload()}>Retry</Button>
      </div>
    );
  }

  if (!graphData) {
    return (
      <div className="flex flex-col items-center justify-center h-screen">
        <div className="text-[#0077B6] mb-4">No graph data available</div>
        <Button onClick={() => window.location.reload()}>Refresh</Button>
      </div>
    );
  }

  return (
    <div className="min-h-screen">
      <div
        style={{
          margin: '10px',
          position: 'relative',
          display: 'flex',
          gap: '10px',
          alignItems: 'center',
        }}
      >
        <select
          value={selectedCohorts}
          onChange={(e) => {
            const value = e.target.value;
            setSelectedCohorts(value === 'all' ? 'all' : Number(value));
          }}
          style={{
            padding: '5px',
            borderRadius: '4px',
            border: '1px solid #0077B6',
            backgroundColor: 'white',
            color: '#0077B6',
          }}
        >
          <option value="all">Show all cohorts</option>
          {[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map((value) => (
            <option key={value} value={value}>
              Show latest {value} cohorts
            </option>
          ))}
        </select>

        {/* Zoom Controls */}
        <div style={{ display: 'flex', gap: '5px', marginLeft: 'auto' }}>
          <Button
            variant="contained"
            onClick={handleZoomIn}
            style={{
              backgroundColor: '#0077B6',
              color: 'white',
              minWidth: '30px',
            }}
          >
            +
          </Button>
          <Button
            variant="contained"
            onClick={handleZoomOut}
            style={{
              backgroundColor: '#0077B6',
              color: 'white',
              minWidth: '30px',
            }}
          >
            -
          </Button>
          <Button
            variant="contained"
            onClick={handleResetZoom}
            style={{
              backgroundColor: '#0077B6',
              color: 'white',
            }}
          >
            Reset Zoom
          </Button>
        </div>
      </div>

      <div style={{ margin: '10px', position: 'relative' }}>
        <Card style={{ borderColor: '#FF8500' }}>
          <CardContent>
            <svg ref={svgRef} width={width} height={height} />
          </CardContent>
          <div ref={tooltipRef}></div>
        </Card>
      </div>
      <Card
        style={{ margin: '10px', position: 'relative', borderColor: '#0077B6' }}
      >
        <CardHeader>
          <CardTitle style={{ color: '#FF8500' }}>Metrics</CardTitle>
        </CardHeader>
        <CardContent
          style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}
        >
          <div className="font-medium text-[#0077B6]">
            Total Beads:{' '}
            <span style={{ fontWeight: 'normal', color: '#FF8500' }}>
              {totalBeads}
            </span>
          </div>
          <div className="font-medium text-[#0077B6]">
            Total Cohorts:{' '}
            <span style={{ fontWeight: 'normal', color: '#FF8500' }}>
              {totalCohorts}
            </span>
          </div>
          <div className="font-medium text-[#0077B6]">
            Max Cohort Size:{' '}
            <span style={{ fontWeight: 'normal', color: '#FF8500' }}>
              {maxCohortSize}
            </span>
          </div>
          <div className="font-medium text-[#0077B6]">
            HWP Length:{' '}
            <span style={{ fontWeight: 'normal', color: '#FF8500' }}>
              {hwpLength}
            </span>
          </div>
        </CardContent>
      </Card>
    </div>
  );
};

export default GraphVisualization;
