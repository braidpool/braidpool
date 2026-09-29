import React, { useRef, useEffect, useState } from 'react';
import * as d3 from 'd3';
import { Loader, WifiOff, AlertCircle } from 'lucide-react';
import { GraphData, GraphNode, NodeIdMapping, BeadRecord } from './Types';
import {
  layoutNodes,
  getEllipseEdgePoint,
  animateLinkDirection,
} from './BraidPoolDAGUtils';
import { WEBSOCKET_URLS } from '../../URLs';
import {
  NODE_RADIUS,
  COLORS,
  MAX_BEADS_RECORDS,
  LINK_STROKE_WIDTH,
  ARROW_WIDTH,
  ARROW_HEIGHT,
  CONTAINER_HEIGHT,
} from './Constants';
import { ChevronDown, ChevronUp } from 'lucide-react';

const GraphVisualization: React.FC = () => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [isPlaying, setIsPlaying] = useState(true);
  const isPlayingRef = useRef(true);
  const width = window.innerWidth - 100;
  const margin = { top: 0, right: 0, bottom: 0, left: 50 };
  const [nodeIdMap, setNodeIdMap] = useState<NodeIdMapping>({});
  const [selectedCohorts, setSelectedCohorts] = useState<number | 'all'>(20);
  const nodeRadius = NODE_RADIUS;
  const tooltipRef = useRef<HTMLDivElement>(null);

  const [graphUpdateCounter, setGraphUpdateCounter] = useState(0);
  const [latestBeadHashForHighlight, setLatestBeadHashForHighlight] = useState<
    string | null
  >(null);

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
  const zoomTransformRef = useRef<d3.ZoomTransform | null>(null);

  const [consecutiveZoomInCount, setConsecutiveZoomInCount] = useState(0);
  const [consecutiveZoomOutCount, setConsecutiveZoomOutCount] = useState(0);

  const hasInitializedTableRef = useRef(false);

  const selectedCohortsRef = useRef<number | 'all'>(selectedCohorts);
  const loadDAGRef = useRef<(() => Promise<void>) | null>(null);

  const [beadRecords, setBeadRecords] = useState<BeadRecord[]>([]);

  const [graphData, setGraphData] = useState<GraphData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [connectionStatus, setConnectionStatus] = useState<
    'connecting' | 'connected' | 'disconnected' | 'error'
  >('connecting');
  const [nodeBraidInfo, setNodeBraidInfo] = useState<{
    bead_count: number;
    cohort_count: number;
  } | null>(null);

  useEffect(() => {
    let mounted = true;
    let ws: WebSocket;
    let reqId = 0;
    let reconnectDelay = 1_000;
    let hasLoaded = false;
    let fetchGen = 0;
    const RPC_TIMEOUT_MS = 15_000;
    const pending = new Map<
      number,
      {
        resolve: (v: unknown) => void;
        reject: (e: Error) => void;
        timer: ReturnType<typeof setTimeout>;
      }
    >();

    function rpc(method: string, params: unknown[] = []): Promise<unknown> {
      return new Promise((resolve, reject) => {
        const id = ++reqId;
        const timer = setTimeout(() => {
          pending.delete(id);
          reject(new Error(`RPC timeout: ${method}`));
        }, RPC_TIMEOUT_MS);
        pending.set(id, { resolve, reject, timer });
        try {
          ws.send(JSON.stringify({ jsonrpc: '2.0', id, method, params }));
        } catch (e) {
          clearTimeout(timer);
          pending.delete(id);
          reject(e);
        }
      });
    }

    async function loadDAG() {
      const myGen = ++fetchGen;
      const sel = selectedCohortsRef.current;
      try {
        const rawBraidInfo = await rpc('getbraidinfo');

        const bi = rawBraidInfo as {
          bead_count: number;
          cohort_count: number;
          total_work: string;
          tip_count: number;
        };
        if (mounted) setNodeBraidInfo(bi);

        const cohortCount = bi.cohort_count ?? 0;

        if (cohortCount === 0) {
          if (mounted && fetchGen === myGen) {
            setGraphData({
              cohorts: [],
              parents: {},
              children: {},
              highest_work_path: [],
              bead_count: bi.bead_count,
            });
            setLoading(false);
            hasLoaded = true;
          }
          return;
        }

        // 'all' → fetch every cohort; number → fetch the last N.
        const numToFetch =
          sel === 'all' ? cohortCount : Math.min(sel, cohortCount);
        const startCohort = Math.max(0, cohortCount - numToFetch);
        const cohorts = (await Promise.all(
          Array.from({ length: cohortCount - startCohort }, (_, i) =>
            rpc('getcohortbyid', [startCohort + i]).catch((e) => {
              console.warn(
                `[BraidPoolDAG] getcohortbyid(${startCohort + i}) failed:`,
                e
              );
              return [];
            })
          )
        )) as string[][];

        const allBeads = cohorts.flat();

        const parentEntries = await Promise.all(
          allBeads.map((hash) =>
            rpc('getparents', [hash])
              .then((p) => [hash, p as string[]] as const)
              .catch(() => [hash, [] as string[]] as const)
          )
        );

        const parents = Object.fromEntries(parentEntries);
        const children: Record<string, string[]> = {};
        for (const [hash, ps] of parentEntries) {
          for (const p of ps) {
            (children[p] ??= []).push(hash);
          }
        }
        const loadedBeadSet = new Set(allBeads);
        const rawHwp = (await rpc('gethighestworkpathbycount', [
          numToFetch,
        ]).catch((e) => {
          console.warn('[BraidPoolDAG] gethighestworkpathbycount failed:', e);
          return [] as string[];
        })) as string[];
        const hwp = rawHwp.filter((h) => loadedBeadSet.has(h));

        if (!mounted || fetchGen !== myGen) return;
        console.log(
          `[BraidPoolDAG] ready: ${allBeads.length} beads across ${cohorts.length} cohorts (node total: ${bi.bead_count})`
        );
        setGraphData({
          cohorts,
          parents,
          children,
          highest_work_path: hwp,
          bead_count: bi.bead_count,
        });
        setLoading(false);
        setError(null);
        hasLoaded = true;
      } catch (err) {
        if (!mounted || fetchGen !== myGen) return;
        console.error('[BraidPoolDAG] loadDAG failed:', err);
        setError(`Failed to load DAG data from node: ${err}`);
        setLoading(false);
      }
    }

    // Expose so other effects can trigger a re-fetch when selection changes.
    loadDAGRef.current = loadDAG;

    function connect() {
      if (!mounted) return;
      setConnectionStatus('connecting');
      ws = new WebSocket(WEBSOCKET_URLS.NODE_RPC_WS);

      ws.onopen = () => {
        if (!mounted) return;
        reconnectDelay = 1_000;
        setConnectionStatus('connected');
        loadDAG();
        const subId = ++reqId;
        const subTimer = setTimeout(
          () => pending.delete(subId),
          RPC_TIMEOUT_MS
        );
        pending.set(subId, {
          resolve: () => {
            clearTimeout(subTimer);
          },
          reject: () => {
            clearTimeout(subTimer);
          },
          timer: subTimer,
        });
        ws.send(
          JSON.stringify({
            jsonrpc: '2.0',
            id: subId,
            method: 'subscribebead',
            params: [],
          })
        );
      };

      ws.onmessage = ({ data }: MessageEvent<string>) => {
        if (!mounted) return;
        let msg: Record<string, unknown>;
        try {
          msg = JSON.parse(data) as Record<string, unknown>;
        } catch {
          return;
        }
        if (msg.id != null) {
          const p = pending.get(msg.id as number);
          if (p) {
            clearTimeout(p.timer);
            pending.delete(msg.id as number);
            if (msg.error) p.reject(new Error(JSON.stringify(msg.error)));
            else p.resolve(msg.result);
          }
          return;
        }
        const params = msg.params as Record<string, unknown> | undefined;
        if (msg.method === 'subscribebead' && params?.result != null) {
          if (isPlayingRef.current) loadDAG();
        }
      };

      ws.onerror = (e) => {
        console.error('[BraidPoolDAG] WebSocket error:', e);
        if (mounted) setConnectionStatus('error');
      };

      ws.onclose = (e) => {
        if (!mounted) return;
        console.warn(`[BraidPoolDAG] disconnected (code ${e.code})`);
        setConnectionStatus('disconnected');
        pending.forEach(({ reject, timer }) => {
          clearTimeout(timer);
          reject(new Error('WebSocket closed'));
        });
        pending.clear();
        if (!hasLoaded) {
          setLoading(false);
          setError(`Cannot reach node at ${WEBSOCKET_URLS.NODE_RPC_WS}. `);
        }
        setTimeout(connect, reconnectDelay);
        reconnectDelay = Math.min(reconnectDelay * 2, 30_000);
      };
    }

    connect();
    return () => {
      mounted = false;
      if (ws) {
        ws.onclose = null;
        ws.close();
      }
    };
  }, []);
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
    if (!graphData) return;

    const firstCohortChanged =
      graphData.cohorts?.[0]?.length > 0 &&
      JSON.stringify(prevFirstCohortRef.current) !==
        JSON.stringify(graphData.cohorts[0]);

    const lastCohortChanged =
      graphData.cohorts.length > 0 &&
      JSON.stringify(prevLastCohortRef.current) !==
        JSON.stringify(graphData.cohorts[graphData.cohorts.length - 1]);

    if (firstCohortChanged) {
      const top = COLORS.shift();
      COLORS.push(top ?? `rgba(${217}, ${95}, ${2}, 1)`);
      prevFirstCohortRef.current = graphData.cohorts[0];
    }

    if (lastCohortChanged) {
      prevLastCohortRef.current =
        graphData.cohorts[graphData.cohorts.length - 1];
    }

    const newMapping: NodeIdMapping = {};
    let nextId = 1;
    Object.keys(graphData.parents).forEach((hash) => {
      if (!newMapping[hash]) {
        newMapping[hash] = nextId.toString();
        nextId++;
      }
    });
    setNodeIdMap(newMapping);

    // Track new beads for the table
    const hwPathSet = new Set(graphData.highest_work_path);
    const newBeads: BeadRecord[] = [];

    if (!hasInitializedTableRef.current && graphData.cohorts.length > 0) {
      hasInitializedTableRef.current = true;
      graphData.cohorts.forEach((cohort, cohortIndex) => {
        cohort.forEach((beadHash: string) => {
          const parentHashes = graphData.parents[beadHash] || [];
          const childHashes = graphData.children[beadHash] || [];
          newBeads.push({
            hash: beadHash,
            parentHashes,
            parentCount: parentHashes.length,
            childHashes,
            childCount: childHashes.length,
            isHWP: hwPathSet.has(beadHash),
            timestamp: new Date().toLocaleTimeString(),
            cohortIndex,
          });
        });
      });

      setBeadRecords(newBeads.reverse().slice(0, MAX_BEADS_RECORDS));
    } else if (lastCohortChanged && graphData.cohorts.length > 0) {
      const lastCohort = graphData.cohorts[graphData.cohorts.length - 1];
      lastCohort.forEach((beadHash: string) => {
        const parentHashes = graphData.parents[beadHash] || [];
        const childHashes = graphData.children[beadHash] || [];
        const cohortIndex = graphData.cohorts.findIndex((c) =>
          c.includes(beadHash)
        );
        newBeads.push({
          hash: beadHash,
          parentHashes,
          parentCount: parentHashes.length,
          childHashes,
          childCount: childHashes.length,
          isHWP: hwPathSet.has(beadHash),
          timestamp: new Date().toLocaleTimeString(),
          cohortIndex,
        });
      });
      if (newBeads.length > 0) {
        setBeadRecords((prev) => {
          const updated = [...newBeads, ...prev];
          return updated.slice(0, MAX_BEADS_RECORDS);
        });
      }
    }

    setGraphUpdateCounter((prevCounter) => {
      const newCounter = prevCounter + 1;
      if (
        (newCounter === 1 || newCounter % 5 === 0) &&
        graphData.highest_work_path.length > 0
      ) {
        setLatestBeadHashForHighlight(
          graphData.highest_work_path[graphData.highest_work_path.length - 1]
        );
      }
      return newCounter;
    });
    setTotalBeads(nodeBraidInfo?.bead_count ?? graphData.bead_count);
    setTotalCohorts(nodeBraidInfo?.cohort_count ?? graphData.cohorts.length);
    setMaxCohortSize(
      graphData.cohorts.length > 0
        ? Math.max(...graphData.cohorts.map((c) => c.length))
        : 0
    );
    setHwpLength(graphData.highest_work_path.length);

    if (firstCohortChanged || lastCohortChanged) {
      setTimeout(() => {
        animateCohorts(
          [],
          lastCohortChanged
            ? graphData.cohorts[graphData.cohorts.length - 1]
            : []
        );
      }, 100);
    }
  }, [graphData, nodeBraidInfo]);
  const animateCohorts = (firstCohort: string[], lastCohort: string[]) => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);

    if (firstCohort.length > 0) {
      svg
        .selectAll('.node')
        .filter((d: any) => firstCohort.includes(d.id))
        .select('ellipse , rect')
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
        .select('ellipse , rect')
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
  useEffect(() => {
    selectedCohortsRef.current = selectedCohorts;
    hasInitializedTableRef.current = false;
    setBeadRecords([]);
    loadDAGRef.current?.();
    zoomTransformRef.current = null;
  }, [selectedCohorts]);

  const handleResetZoom = () => {
    const nextZoom = 0.3;
    setDefaultZoom(nextZoom);
    zoomTransformRef.current = null;
    setConsecutiveZoomInCount(0);
    setConsecutiveZoomOutCount(0);
  };

  const handleZoomIn = () => {
    if (consecutiveZoomInCount >= 3) {
      return;
    }

    setDefaultZoom((prevZoom) => {
      const nextZoom = Math.min(prevZoom + 0.1, 5);
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
    const containerWidth = svgRef.current.parentElement?.clientWidth ?? width;
    svgRef.current.setAttribute('width', String(containerWidth));

    const filteredCohorts =
      selectedCohorts === 'all'
        ? graphData.cohorts
        : graphData.cohorts.slice(-selectedCohorts);
    const filteredCohortNodes = new Set(filteredCohorts.flat());

    const tooltip = d3.select(tooltipRef.current).style('visibility', 'hidden');

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const container = svg.append('g');

    const allNodes = Object.keys(graphData.parents).map((id) => ({
      id,
      parents: graphData.parents[id],
      children: graphData.children[id] ?? [],
    }));

    const hwPath = graphData.highest_work_path;
    const cohorts = graphData.cohorts;
    const positions = layoutNodes(
      allNodes,
      hwPath,
      {},
      CONTAINER_HEIGHT,
      {},
      margin
    );
    const hwPathSet = new Set(hwPath);

    const visibleNodes = allNodes.filter((node) =>
      filteredCohortNodes.has(node.id)
    );
    let minVisibleX = Infinity;
    let maxVisibleX = -Infinity;
    visibleNodes.forEach((node) => {
      const x = positions[node.id]?.x ?? 0;
      if (x < minVisibleX) minVisibleX = x;
      if (x > maxVisibleX) maxVisibleX = x;
    });
    if (!isFinite(minVisibleX)) minVisibleX = margin.left;
    if (!isFinite(maxVisibleX)) maxVisibleX = margin.left;
    const offsetX = margin.left - minVisibleX;

    zoomBehavior.current = d3
      .zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.1, 5])
      .on('zoom', (event: d3.D3ZoomEvent<SVGSVGElement, unknown>) => {
        container.attr('transform', event.transform.toString());
        if (event.sourceEvent) {
          zoomTransformRef.current = event.transform;
        }
      });
    const scale = defaultZoom;
    const rightPad = 80;
    const visibleSpanScaled =
      (maxVisibleX - minVisibleX + 2 * (nodeRadius + 10)) * scale;
    let autoTx: number;
    if (visibleSpanScaled + rightPad < containerWidth) {
      const contentCenterX = (minVisibleX + maxVisibleX) / 2 + offsetX;
      autoTx = containerWidth / 2 - contentCenterX * scale;
    } else {
      autoTx =
        containerWidth -
        rightPad -
        (maxVisibleX + offsetX + nodeRadius + 10) * scale;
    }
    const autoTy = CONTAINER_HEIGHT / 2 - (CONTAINER_HEIGHT / 2) * scale - 60;
    const autoTransform = d3.zoomIdentity
      .translate(autoTx, autoTy)
      .scale(scale);

    svg
      .call(zoomBehavior.current)
      .call(
        zoomBehavior.current.transform,
        zoomTransformRef.current ?? autoTransform
      );

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
      .attr('stroke-width', LINK_STROKE_WIDTH)
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
      .attr('dy', '0.35em')
      .attr('text-anchor', 'middle')
      .text((d) => `${d.id.slice(-4)}`)
      .attr('fill', '#fff')
      .style('font-size', 55)
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
                            <span style="color: #FF8500;">→</span>
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
      .attr('markerWidth', ARROW_WIDTH)
      .attr('markerHeight', ARROW_HEIGHT)
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

  if (loading && !graphData) {
    return (
      <div className="flex items-center justify-center h-full w-full">
        <div className="flex flex-col items-center">
          <Loader className="h-8 w-8 text-[#0077B6] animate-spin" />
          <p className="mt-4 text-[#0077B6]">
            {connectionStatus === 'connecting'
              ? 'Connecting to node…'
              : 'Loading DAG data…'}
          </p>
          <p className="mt-1 text-xs text-gray-500">
            {WEBSOCKET_URLS.NODE_RPC_WS}
          </p>
        </div>
      </div>
    );
  }

  if (error && !graphData) {
    return (
      <div className="flex flex-col items-center justify-center h-screen gap-3">
        <AlertCircle className="h-10 w-10 text-red-500" />
        <div className="text-red-400 text-sm max-w-sm text-center">{error}</div>
        <p className="text-xs text-gray-500">
          Make sure the node is running at{' '}
          <code className="font-mono">{WEBSOCKET_URLS.NODE_RPC_WS}</code>
        </p>
      </div>
    );
  }

  if (!graphData) {
    return (
      <div className="flex flex-col items-center justify-center h-screen gap-3">
        <WifiOff className="h-10 w-10 text-gray-500" />
        <div className="text-gray-400">Waiting for node data…</div>
      </div>
    );
  }

  const connectionBanner =
    connectionStatus === 'disconnected' || connectionStatus === 'error' ? (
      <div className="flex items-center gap-2 px-3 py-1.5 border  rounded  text-xs">
        <WifiOff className="h-3.5 w-3.5 shrink-0" />
        <span>Node disconnected showing last known state. Reconnecting…</span>
      </div>
    ) : connectionStatus === 'connecting' ? (
      <div className="flex items-center gap-2 px-3 py-1.5 bg-blue-900/40 border border-blue-600 rounded text-blue-300 text-xs">
        <Loader className="h-3.5 w-3.5 animate-spin shrink-0" />
        <span>Connecting to node…</span>
      </div>
    ) : null;

  return (
    <div>
      {connectionBanner && <div className="mx-2 mt-2">{connectionBanner}</div>}
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
              {[5, 10, 15, 20].map((value) => (
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
                    {totalBeads.toLocaleString()}
                  </span>
                </div>
                <div className="font-medium text-[#0077B6]">
                  Total Cohorts:{' '}
                  <span className="font-normal text-[#FF8500]">
                    {totalCohorts.toLocaleString()}
                  </span>
                </div>
                <div className="font-medium text-[#0077B6]">
                  Max Cohort Size:{' '}
                  <span className="font-normal text-[#FF8500]">
                    {maxCohortSize}
                  </span>
                </div>
                <div className="font-medium text-[#0077B6]">
                  HWP (window):{' '}
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
            height={CONTAINER_HEIGHT}
            overflow="visible"
            className="block"
          />
          <div
            ref={tooltipRef}
            className="fixed bg-gray-800 text-white border rounded p-2 shadow-lg pointer-events-none z-10 bottom-5 right-5 mb-[200px] border-gray-600 backdrop-blur-lg"
          ></div>
        </div>
      </div>
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
                          {bead.cohortIndex !== undefined &&
                          bead.cohortIndex !== -1
                            ? bead.cohortIndex
                            : 'N/A'}
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
