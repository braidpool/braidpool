import React, { useRef, useEffect, useState } from 'react';
import * as d3 from 'd3';
import { io, Socket } from 'socket.io-client';
import { Card, CardContent, CardHeader, CardTitle } from '../components/ui/card';
import { Button } from '../components/ui/button';
import { ReloadIcon } from '@radix-ui/react-icons';

interface GraphNode {
    id: string;
    parents: string[];
    children: string[];
    work?: number;
}

interface GraphData {
    highest_work_path: string[] | number[];
    parents: Record<string, string[] | number[]>;
    children: Record<string, string[] | number[]>;
    work?: Record<string, number>;
    cohorts: (string[] | number[])[];
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
    const COLORS = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728'];

    const nodeRadius = 15;
    const margin = { top: 0, right: 0, bottom: 0, left: 50 };
    const tooltipRef = useRef<HTMLDivElement>(null);

    const COLUMN_WIDTH = 120;
    const VERTICAL_SPACING = 100;

    const layoutNodes = (allNodes: GraphNode[], hwPath: string[], cohorts: string[][]): Record<string, Position> => {
        const positions: Record<string, Position> = {};
        const columnOccupancy: Record<number, number> = {};
        const hwPathSet = new Set(hwPath);
        const centerY = height / 2;
        const cohortMap = new Map<string, number>();
        cohorts.forEach((cohort, index) => {
            cohort.forEach(nodeId => cohortMap.set(nodeId, index));
        });

        let currentX = margin.left;
        let prevCohort: number | undefined;
        const hwPathColumns: number[] = [];

        hwPath.forEach((nodeId, index) => {
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

        const generations = new Map<string, number>();
        const remainingNodes = allNodes.filter(node => !hwPathSet.has(node.id));

        remainingNodes.forEach(node => {
            const hwpParents = node.parents.filter(p => hwPathSet.has(p));
            if (hwpParents.length > 0) {
                const minHWPIndex = Math.min(...hwpParents.map(p => hwPath.indexOf(p)));
                generations.set(node.id, minHWPIndex + 1);
            } else {
                const parentGens = node.parents.map(p => generations.get(p) || 0);
                generations.set(node.id, parentGens.length > 0 ? Math.max(...parentGens) + 1 : 0);
            }
        });

        remainingNodes.sort((a, b) => (generations.get(a.id) || 0) - (generations.get(b.id) || 0));

        const tipNodes: string[] = [];

        remainingNodes.forEach(node => {
            if (node.parents.length === 1 && node.children.length === 0) {
                tipNodes.push(node.id);
            }
            const positionedParents = node.parents.filter(p => positions[p]);
            if (positionedParents.length === 0) return;

            const maxParentX = Math.max(...positionedParents.map(p => positions[p].x));

            let targetX = maxParentX + COLUMN_WIDTH;

            const hwpParents = positionedParents.filter(p => hwPathSet.has(p));
            if (hwpParents.length > 0) {
                const rightmostHWPParentX = Math.max(...hwpParents.map(p => positions[p].x));
                const parentIndex = hwPathColumns.indexOf(rightmostHWPParentX);
                if (parentIndex >= 0 && parentIndex < hwPathColumns.length - 1) {
                    targetX = hwPathColumns[parentIndex + 1];
                }
            }

            let yPos = centerY;
            const maxParentY = Math.max(...positionedParents.map(p => positions[p].y));
            yPos = maxParentY + VERTICAL_SPACING;

            const colKey = Math.round((targetX - margin.left) / COLUMN_WIDTH);
            if (columnOccupancy[colKey] === undefined) {
                columnOccupancy[colKey] = 0;
            } else {
                yPos = maxParentY + VERTICAL_SPACING + (columnOccupancy[colKey] * VERTICAL_SPACING);
            }
            columnOccupancy[colKey] += 1;

            positions[node.id] = { x: targetX, y: Math.min(yPos, Math.abs(height - yPos)) };
        });

        const maxColumnX = Math.max(...Object.values(positions).map(pos => pos.x));
        tipNodes.forEach(tipId => {
            if (positions[tipId]) {
                positions[tipId].x = maxColumnX;
            }
        });

        return positions;
    };

    const [_socket, setSocket] = useState<Socket | null>(null);
    const [_connectionStatus, setConnectionStatus] = useState('Disconnected');

    const [totalBeads, setTotalBeads] = useState<number>(0);
    const [totalCohorts, setTotalCohorts] = useState<number>(0);
    const [maxCohortSize, setMaxCohortSize] = useState<number>(0);
    const [hwpLength, setHwpLength] = useState<number>(0);

    const [defaultZoom, setDefaultZoom] = useState(0.5);
    const zoomBehavior = useRef<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(null);

    useEffect(() => {
        const newSocket = io('http://localhost:65433', {
            reconnection: true,
            reconnectionAttempts: Infinity,
            reconnectionDelay: 1000,
            reconnectionDelayMax: 5000,
            timeout: 20000
        });

        setSocket(newSocket);

        newSocket.on('connect', () => {
            setConnectionStatus('Connected');
        });

        newSocket.on('disconnect', () => {
            setConnectionStatus('Disconnected');
        });

        newSocket.on('connect_error', (err) => {
            setConnectionStatus(`Error: ${err.message}`);
        });

        newSocket.on('braid_update', (data: { data: string }) => {
            try {
                const parsedData = JSON.parse(data.data) as GraphData;
                setGraphData(parsedData);
                let beads = 0;
                for (const _key in parsedData.work) {
                    beads += 1;
                }
                setTotalBeads(beads);
                setTotalCohorts(parsedData.cohorts.length);
                let maxSize = 0;
                parsedData.cohorts.forEach(cohort => {
                    if (cohort.length > maxSize) {
                        maxSize = cohort.length;
                    }
                });
                setMaxCohortSize(maxSize);
                setHwpLength(parsedData.highest_work_path.length);
                setLoading(false);
            } catch (err) {
                setError('Error parsing graph data');
                setLoading(false);
            }
        });

        return () => {
            newSocket.disconnect();
        };
    }, []);

    const resetZoom = () => {
        if (svgRef.current && zoomBehavior.current) {
            d3.select(svgRef.current)
                .transition()
                .duration(500)
                .call(zoomBehavior.current.transform, d3.zoomIdentity.scale(defaultZoom));
        }
    };

    const zoomIn = () => {
        setDefaultZoom((prevZoom) => Math.min(prevZoom + 0.1, 5));
    };

    const zoomOut = () => {
        setDefaultZoom((prevZoom) => Math.max(prevZoom - 0.1, 0.5));
    };

    useEffect(() => {
        if (!svgRef.current || !graphData) return;

        const tooltip = d3.select(tooltipRef.current)
            .style('position', 'absolute')
            .style('visibility', 'hidden')
            .style('background', '#0077B6') // Light blue background
            .style('color', 'white')
            .style('border', '1px solid #FF8500') // Orange border
            .style('border-radius', '5px')
            .style('padding', '10px')
            .style('box-shadow', '2px 2px 5px rgba(0,0,0,0.2)')
            .style('pointer-events', 'none')
            .style('z-index', '10');

        const stringData = {
            highest_work_path: graphData.highest_work_path.map(String),
            parents: Object.fromEntries(
                Object.entries(graphData.parents).map(([k, v]) => [k, v.map(String)])
            ),
            children: Object.fromEntries(
                Object.entries(graphData.children).map(([k, v]) => [k, v.map(String)])
            ),
            work: graphData.work || {},
            cohorts: graphData.cohorts.map(cohort => cohort.map(String)),
        };

        const svg = d3.select(svgRef.current);
        svg.selectAll('*').remove();

        const container = svg.append('g');

        zoomBehavior.current = d3.zoom<SVGSVGElement, unknown>()
            .scaleExtent([0.5, 5])
            .on('zoom', (event: d3.D3ZoomEvent<SVGSVGElement, unknown>) => {
                container.attr('transform', event.transform.toString());
            });

        svg.call(zoomBehavior.current).call(zoomBehavior.current.transform, d3.zoomIdentity.scale(defaultZoom));

        const allNodes = Object.keys(stringData.parents).map(id => ({
            id,
            parents: stringData.parents[id],
            children: stringData.children[id],
            work: stringData.work[id] || 0,
        }));

        const hwPath = stringData.highest_work_path as string[];
        const positions = layoutNodes(allNodes, hwPath, stringData.cohorts as string[][]);
        const hwPathSet = new Set(hwPath);

        const links: { source: string; target: string }[] = [];
        allNodes.forEach(node => {
            node.children.forEach(childId => {
                links.push({ source: node.id, target: childId });
            });
        });

        container.append('defs').selectAll('marker')
            .data(['end'])
            .enter()
            .append('marker')
            .attr('id', 'arrow')
            .attr('viewBox', '0 -5 10 10')
            .attr('refX', nodeRadius + 2)
            .attr('refY', 0)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M0,-5L10,0L0,5')
            .attr('fill', '#FF8500'); // Orange arrow

        container.selectAll('.link')
            .data(links)
            .enter()
            .append('line')
            .attr('class', 'link')
            .attr('x1', d => positions[d.source]?.x || 0)
            .attr('y1', d => positions[d.source]?.y || 0)
            .attr('x2', d => positions[d.target]?.x || 0)
            .attr('y2', d => positions[d.target]?.y || 0)
            .attr('stroke', '#48CAE4') // Light blue links
            .attr('stroke-width', 1.5)
            .attr('marker-end', 'url(#arrow)');

        const nodes = container.selectAll('.node')
            .data(allNodes)
            .enter()
            .append('g')
            .attr('class', 'node')
            .attr('transform', d => `translate(${positions[d.id].x},${positions[d.id].y})`);

        const cohortMap = new Map<string, number>();
        (stringData.cohorts as string[][]).forEach((cohort, index) => {
            cohort.forEach(nodeId => cohortMap.set(nodeId, index));
        });

        nodes.append('circle')
            .attr('r', nodeRadius)
            .attr("fill", d => {
                const cohortIndex = cohortMap.get(d.id);
                return COLORS[(cohortIndex !== undefined ? cohortIndex : 0) % COLORS.length];
            })
            .attr('stroke', '#fff')
            .attr('stroke-width', 2)
            .on('mouseover', function (event: MouseEvent, d: GraphNode) {
                d3.select(this)
                    .attr('stroke', '#FF8500') // Orange border on hover
                    .attr('stroke-width', 3);

                const cohortIndex = cohortMap.get(d.id);
                const isHWP = hwPathSet.has(d.id);

                const tooltipContent = `
                    <div><strong>ID:</strong> ${d.id}</div>
                    <div><strong>Work:</strong> ${d.work}</div>
                    <div><strong>Cohort:</strong> ${cohortIndex !== undefined ? cohortIndex : 'N/A'}</div>
                    <div><strong>Highest Work Path:</strong> ${isHWP ? 'Yes' : 'No'}</div>
                    <div><strong>Parents:</strong> ${d.parents.length > 0 ? d.parents.join(', ') : 'None'}</div>
                    <div><strong>Children:</strong> ${d.children.length > 0 ? d.children.join(', ') : 'None'}</div>
                `;

                tooltip
                    .html(tooltipContent)
                    .style('visibility', 'visible')
                    .style('left', `${event.pageX + 10}px`)
                    .style('top', `${event.pageY + 10}px`);
            })
            .on('mouseout', function () {
                d3.select(this)
                    .attr('stroke', '#fff')
                    .attr('stroke-width', 2);
                tooltip.style('visibility', 'hidden');
            })
            .on('mousemove', function (event: MouseEvent) {
                tooltip
                    .style('left', `${event.pageX + 10}px`)
                    .style('top', `${event.pageY + 10}px`);
            });

        nodes.append('text')
            .attr('dy', 4)
            .attr('text-anchor', 'middle')
            .text(d => d.id)
            .attr('fill', '#fff')
            .style('font-size', '10px');

        container.append('text')
            .attr('x', width / 2)
            .attr('y', margin.top / 2)
            .attr('text-anchor', 'middle')
            .style('font-size', '16px')
    }, [graphData, defaultZoom]);

    if (loading) {
        return (
            <div className="fixed inset-0 flex items-center justify-center">
                <div className="flex flex-col items-center">
                    <ReloadIcon className="h-8 w-8 animate-spin text-[#FF8500]" />
                    <p className="mt-4 text-[#0077B6]">Loading graph data...</p>
                </div>
            </div>
        );
    }


    if (error) {
        return (
            <div className="flex flex-col items-center justify-center h-screen">
                <div className="text-red-500 mb-4">Error: {error}</div>
                <Button
                    onClick={() => window.location.reload()}
                    style={{ backgroundColor: '#FF8500', color: 'white' }}
                >
                    Retry
                </Button>
            </div>
        );
    }

    if (!graphData) {
        return (
            <div className="flex flex-col items-center justify-center h-screen">
                <div className="text-[#0077B6] mb-4">No graph data available</div>
                <Button
                    onClick={() => window.location.reload()}
                    style={{ backgroundColor: '#FF8500', color: 'white' }}
                >
                    Refresh
                </Button>
            </div>
        );
    }

    return (
        <div className="min-h-screen">
            <div className='pt-25' style={{ margin: '10px', position: 'relative', display: 'flex', gap: '10px', alignItems: 'center' }}>
                <Button
                    onClick={zoomOut}
                    style={{ backgroundColor: '#FF8500', color: 'white', border: '1px solid #E76F00' }}
                    className="hover:bg-[#E76F00] transition-colors"
                >
                    -
                </Button>
                <Button
                    onClick={zoomIn}
                    style={{ backgroundColor: '#FF8500', color: 'white', border: '1px solid #E76F00' }}
                    className="hover:bg-[#E76F00] transition-colors"
                >
                    +
                </Button>
                <Button
                    onClick={resetZoom}
                    style={{ backgroundColor: '#0077B6', color: 'white', border: '1px solid #023E8A' }}
                    className="hover:bg-[#023E8A] transition-colors"
                >
                    Reset Zoom
                </Button>
            </div>
            <div style={{ margin: '10px', position: 'relative' }}>
                <Card style={{ borderColor: '#FF8500' }}>
                    <CardContent>
                        <svg
                            ref={svgRef}
                            width={width}
                            height={height}
                        />
                    </CardContent>
                    <div ref={tooltipRef}></div>
                </Card>
            </div>
            <Card style={{ margin: '10px', position: 'relative', borderColor: '#0077B6' }}>
                <CardHeader>
                    <CardTitle style={{ color: '#FF8500' }}>Metrics</CardTitle>
                </CardHeader>
                <CardContent style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
                    <div className="font-medium text-[#0077B6]">Total Beads: <span style={{ fontWeight: 'normal', color: '#FF8500' }}>{totalBeads}</span></div>
                    <div className="font-medium text-[#0077B6]">Total Cohorts: <span style={{ fontWeight: 'normal', color: '#FF8500' }}>{totalCohorts}</span></div>
                    <div className="font-medium text-[#0077B6]">Max Cohort Size: <span style={{ fontWeight: 'normal', color: '#FF8500' }}>{maxCohortSize}</span></div>
                    <div className="font-medium text-[#0077B6]">HWP Length: <span style={{ fontWeight: 'normal', color: '#FF8500' }}>{hwpLength}</span></div>
                </CardContent>
            </Card>
        </div>
    );
};

export default GraphVisualization;