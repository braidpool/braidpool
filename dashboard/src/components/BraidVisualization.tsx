import React, { useEffect, useRef, useState } from 'react';
import * as d3 from 'd3';
import { BraidVisualizationData, BraidNode, BraidLink } from '../types/braid';
import {
  Box,
  Typography,
  Divider,
  useTheme,
  useMediaQuery,
} from '@mui/material';

interface BraidVisualizationProps {
  data: BraidVisualizationData;
  width?: number;
  height?: number;
}

const BraidVisualization: React.FC<BraidVisualizationProps> = ({
  data,
  width = 800,
  height = 600,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const theme = useTheme();
  const isSmallScreen = useMediaQuery(theme.breakpoints.down('md'));

  // Calculate available width for SVG (container width minus legend and margins)
  const [svgWidth, setSvgWidth] = useState(width);

  // Update SVG width when container size changes
  useEffect(() => {
    const updateDimensions = () => {
      if (containerRef.current) {
        // Account for legend width (160px) and margins
        const legendSpace = 180;
        const containerWidth = containerRef.current.clientWidth;
        setSvgWidth(Math.max(300, containerWidth - legendSpace));
      }
    };

    updateDimensions();
    window.addEventListener('resize', updateDimensions);

    return () => {
      window.removeEventListener('resize', updateDimensions);
    };
  }, []);

  // Color scheme for cohorts
  const colorScale = d3.scaleOrdinal(d3.schemeCategory10);

  useEffect(() => {
    if (!svgRef.current || !data.nodes.length) return;

    // Clear previous visualization
    d3.select(svgRef.current).selectAll('*').remove();

    const svg = d3.select(svgRef.current);

    // Create a hierarchical layout
    const dagLayout = createDagLayout(data, svgWidth, height);

    // Create tooltip
    const tooltip = d3
      .select('body')
      .append('div')
      .attr('class', 'tooltip')
      .style('position', 'absolute')
      .style('background-color', 'white')
      .style('border', '1px solid #ddd')
      .style('border-radius', '4px')
      .style('padding', '6px')
      .style('pointer-events', 'none')
      .style('opacity', 0);

    // Draw links first (so they're behind nodes)
    const links = svg
      .append('g')
      .selectAll('line')
      .data(data.links)
      .enter()
      .append('line')
      .attr('x1', (d) => dagLayout.get(d.source)?.x || 0)
      .attr('y1', (d) => dagLayout.get(d.source)?.y || 0)
      .attr('x2', (d) => dagLayout.get(d.target)?.x || 0)
      .attr('y2', (d) => dagLayout.get(d.target)?.y || 0)
      .attr('stroke', (d) => (d.isHighWorkPath ? '#ff6b6b' : '#999'))
      .attr('stroke-width', (d) => (d.isHighWorkPath ? 2.5 : 1))
      .attr('stroke-opacity', 0.6)
      .attr('marker-end', 'url(#arrow)');

    // Add arrow marker for the links
    svg
      .append('defs')
      .append('marker')
      .attr('id', 'arrow')
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 20)
      .attr('refY', 0)
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', '#999');

    // Draw the nodes
    const nodes = svg
      .append('g')
      .selectAll('circle')
      .data(data.nodes)
      .enter()
      .append('circle')
      .attr('r', (d) => (d.isTip ? 10 : 8))
      .attr('cx', (d) => dagLayout.get(d.id)?.x || 0)
      .attr('cy', (d) => dagLayout.get(d.id)?.y || 0)
      .attr('fill', (d) => colorScale(d.cohort.toString()))
      .attr('stroke', (d) => (d.isTip ? '#ff6b6b' : '#fff'))
      .attr('stroke-width', (d) => (d.isTip ? 3 : 1.5))
      .on('mouseover', (event, d) => {
        tooltip.transition().duration(200).style('opacity', 0.9);
        tooltip
          .html(
            `
          <div>
            <strong>ID:</strong> ${d.id}<br/>
            <strong>Cohort:</strong> ${d.cohort}<br/>
            <strong>Parents:</strong> ${d.parents.join(', ')}<br/>
            <strong>Children:</strong> ${d.children.join(', ')}<br/>
            <strong>Tip:</strong> ${d.isTip ? 'Yes' : 'No'}
          </div>
        `
          )
          .style('left', event.pageX + 10 + 'px')
          .style('top', event.pageY - 28 + 'px');
      })
      .on('mouseout', () => {
        tooltip.transition().duration(500).style('opacity', 0);
      });

    // Add text labels for node IDs
    const labels = svg
      .append('g')
      .selectAll('text')
      .data(data.nodes)
      .enter()
      .append('text')
      .attr('x', (d) => dagLayout.get(d.id)?.x || 0)
      .attr('y', (d) => dagLayout.get(d.id)?.y || 0)
      .attr('dy', '.35em')
      .attr('text-anchor', 'middle')
      .style('fill', 'white')
      .style('font-size', '10px')
      .style('pointer-events', 'none')
      .text((d) => d.id.toString());

    // Adding a title
    svg
      .append('text')
      .attr('x', svgWidth / 2)
      .attr('y', 30)
      .attr('text-anchor', 'middle')
      .style('font-size', '20px')
      .style('font-weight', 'bold')
      .text('Braid Visualization');

    // Add some debugging info
    console.log('🔄 Rendering visualization with:', {
      nodes: data.nodes.length,
      links: data.links.length,
      svgWidth,
      height,
    });

    return () => {
      // Cleanup
      tooltip.remove();
    };
  }, [data, svgWidth, height]);

  // Generate legend items for cohorts
  const renderCohortLegendItems = () => {
    return data.cohorts.map((cohort, index) => (
      <Box key={index} sx={{ display: 'flex', alignItems: 'center', mb: 1 }}>
        <Box
          sx={{
            width: 12,
            height: 12,
            backgroundColor: colorScale(index.toString()),
            mr: 1,
          }}
        />
        <Typography variant='body2'>{`Cohort ${index}`}</Typography>
      </Box>
    ));
  };

  return (
    <Box
      ref={containerRef}
      sx={{
        display: 'flex',
        flexDirection: isSmallScreen ? 'column' : 'row',
        alignItems: isSmallScreen ? 'center' : 'flex-start',
        width: '100%',
        overflow: 'hidden',
      }}>
      <Box
        sx={{
          flex: '1 1 auto',
          overflow: 'hidden',
          display: 'flex',
          justifyContent: 'center',
          maxWidth: '100%',
        }}>
        <svg
          ref={svgRef}
          width={svgWidth}
          height={height}
          style={{
            backgroundColor: '#f8f9fa',
            borderRadius: '8px',
            maxWidth: '100%',
          }}
        />
      </Box>
      <Box
        sx={{
          p: 2,
          ml: isSmallScreen ? 0 : 2,
          mt: isSmallScreen ? 2 : 0,
          border: '1px solid #ddd',
          borderRadius: '8px',
          backgroundColor: 'white',
          minWidth: '140px',
          maxWidth: isSmallScreen ? '100%' : '160px',
          flex: isSmallScreen ? '1 1 auto' : '0 0 160px',
        }}>
        <Typography variant='subtitle1' fontWeight='bold' sx={{ mb: 1 }}>
          Legend
        </Typography>

        {renderCohortLegendItems()}

        <Divider sx={{ my: 1 }} />

        <Box sx={{ display: 'flex', alignItems: 'center', mb: 1 }}>
          <Box
            component='hr'
            sx={{
              width: 15,
              height: 2,
              backgroundColor: '#ff6b6b',
              border: 'none',
              mr: 1,
            }}
          />
          <Typography variant='body2'>High-work path</Typography>
        </Box>

        <Box sx={{ display: 'flex', alignItems: 'center' }}>
          <Box
            sx={{
              width: 12,
              height: 12,
              borderRadius: '50%',
              backgroundColor: colorScale('0'),
              border: '2px solid #ff6b6b',
              mr: 1,
            }}
          />
          <Typography variant='body2'>Tip nodes</Typography>
        </Box>
      </Box>
    </Box>
  );
};

// Helper function to create a DAG layout
const createDagLayout = (
  data: BraidVisualizationData,
  width: number,
  height: number
): Map<number, { x: number; y: number }> => {
  const nodePositions = new Map<number, { x: number; y: number }>();

  // Calculate cohort sizes and maximum cohort size
  const cohortSizes = data.cohorts.map((cohort) => cohort.length);
  const maxCohortSize = Math.max(...cohortSizes);

  // Calculate spacing
  const horizontalSpacing = width / (data.cohorts.length + 1);
  const verticalSpacing = height / (maxCohortSize + 1);

  // Position nodes by cohort
  data.cohorts.forEach((cohort, cohortIndex) => {
    const x = horizontalSpacing * (cohortIndex + 1);

    cohort.forEach((nodeId, nodeIndex) => {
      // Center the nodes in each cohort
      const offset = (maxCohortSize - cohort.length) / 2;
      const y = verticalSpacing * (nodeIndex + offset + 1);

      nodePositions.set(nodeId, { x, y });
    });
  });

  return nodePositions;
};

export default BraidVisualization;
