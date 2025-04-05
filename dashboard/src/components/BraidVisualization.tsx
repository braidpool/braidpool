import React, { useEffect, useRef, useState } from 'react';
import * as d3 from 'd3';
import { BraidVisualizationData } from '../types/braid';
import {
  Box,
  Typography,
  Divider,
  useTheme,
  useMediaQuery,
  Paper,
} from '@mui/material';
import colors from '../theme/colors';

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
  const isExtraSmallScreen = useMediaQuery(theme.breakpoints.down('sm'));

  // Calculate available width for SVG (container width minus legend and margins)
  const [svgWidth, setSvgWidth] = useState(width);

  // Update SVG width when container size changes
  useEffect(() => {
    const updateDimensions = () => {
      if (containerRef.current) {
        // Account for legend width and margins
        const legendSpace = isSmallScreen ? 0 : 160; // Reduced space for legend
        const containerWidth = containerRef.current.clientWidth;
        setSvgWidth(Math.max(300, containerWidth - legendSpace));
      }
    };

    updateDimensions();
    window.addEventListener('resize', updateDimensions);

    return () => {
      window.removeEventListener('resize', updateDimensions);
    };
  }, [isSmallScreen]);

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
      .style('background-color', colors.paper)
      .style('border', `1px solid ${colors.border}`)
      .style('border-radius', '4px')
      .style('padding', '6px')
      .style('pointer-events', 'none')
      .style('opacity', 0)
      .style('color', colors.textPrimary);

    // Draw links first (so they're behind nodes)
    svg
      .append('g')
      .selectAll('line')
      .data(data.links)
      .enter()
      .append('line')
      .attr('x1', (d) => dagLayout.get(d.source)?.x || 0)
      .attr('y1', (d) => dagLayout.get(d.source)?.y || 0)
      .attr('x2', (d) => dagLayout.get(d.target)?.x || 0)
      .attr('y2', (d) => dagLayout.get(d.target)?.y || 0)
      .attr('stroke', (d) =>
        d.isHighWorkPath ? colors.tipNode : colors.linkColor
      )
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
      .attr('fill', colors.linkColor);

    // Draw the nodes
    svg
      .append('g')
      .selectAll('circle')
      .data(data.nodes)
      .enter()
      .append('circle')
      .attr('r', (d) => (d.isTip ? 10 : 8))
      .attr('cx', (d) => dagLayout.get(d.id)?.x || 0)
      .attr('cy', (d) => dagLayout.get(d.id)?.y || 0)
      .attr('fill', (d) => colorScale(d.cohort.toString()))
      .attr('stroke', (d) => (d.isTip ? colors.tipNode : colors.nodeStroke))
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
    svg
      .append('g')
      .selectAll('text')
      .data(data.nodes)
      .enter()
      .append('text')
      .attr('x', (d) => dagLayout.get(d.id)?.x || 0)
      .attr('y', (d) => dagLayout.get(d.id)?.y || 0)
      .attr('dy', '.35em')
      .attr('text-anchor', 'middle')
      .style('fill', colors.textPrimary)
      .style('font-size', '10px')
      .style('pointer-events', 'none')
      .text((d) => d.id.toString());

    // Adding a title
    svg
      .append('text')
      .attr('x', svgWidth / 2)
      .attr('y', 30)
      .attr('text-anchor', 'middle')
      .style('fill', colors.textPrimary)
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
  }, [data, svgWidth, height, colorScale]);

  // Generate legend items for cohorts
  const renderCohortLegendItems = () => {
    // Calculate how to split cohorts into columns
    const columns = isExtraSmallScreen ? 2 : isSmallScreen ? 3 : 1;
    const itemsPerColumn = Math.ceil(data.cohorts.length / columns);

    // Create column arrays
    const columnItems = Array.from({ length: columns }, (_, colIndex) => {
      const startIdx = colIndex * itemsPerColumn;
      const endIdx = Math.min(startIdx + itemsPerColumn, data.cohorts.length);
      return Array.from({ length: endIdx - startIdx }, (_, i) => {
        const index = startIdx + i;
        return (
          <Box
            key={index}
            sx={{
              display: 'flex',
              alignItems: 'center',
              mb: 0.75,
              mr: 1,
              minWidth: 'auto',
              width: '100%',
            }}>
            <Box
              sx={{
                width: 10,
                height: 10,
                backgroundColor: colorScale(index.toString()),
                mr: 0.75,
                border: `1px solid ${colors.border}`,
                flexShrink: 0,
              }}
            />
            <Typography
              variant='caption'
              sx={{
                whiteSpace: 'nowrap',
                overflow: 'hidden',
                textOverflow: 'ellipsis',
                color: colors.textPrimary,
              }}>{`Cohort ${index}`}</Typography>
          </Box>
        );
      });
    });

    // Render items in a flex container for columns
    return (
      <Box
        sx={{
          display: 'flex',
          flexWrap: 'wrap',
          maxHeight: isSmallScreen ? '120px' : '280px',
          overflowY: 'auto',
          overflowX: 'hidden',
          '&::-webkit-scrollbar': {
            width: '6px',
          },
          '&::-webkit-scrollbar-thumb': {
            backgroundColor: 'rgba(255,255,255,0.2)',
            borderRadius: '3px',
          },
        }}>
        {columnItems.flat()}
      </Box>
    );
  };

  return (
    <Box
      ref={containerRef}
      sx={{
        display: 'flex',
        flexDirection: isSmallScreen ? 'column' : 'row',
        alignItems: 'flex-start',
        width: '100%',
        height: '100%',
        overflow: 'hidden',
        borderRadius: 1,
        boxShadow: `0 1px 3px ${colors.shadow}`,
        bgcolor: colors.background,
      }}>
      <Box
        sx={{
          flex: '1 1 auto',
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          maxWidth: '100%',
          height: isSmallScreen ? 'auto' : '100%',
          p: 1,
        }}>
        <svg
          ref={svgRef}
          width={svgWidth}
          height={height}
          style={{
            backgroundColor: colors.chartBackground,
            borderRadius: '6px',
            maxWidth: '100%',
            boxShadow: `inset 0 0 0 1px ${colors.border}`,
          }}
        />
      </Box>
      <Paper
        elevation={0}
        sx={{
          p: 1,
          ml: isSmallScreen ? 1 : 0,
          mt: isSmallScreen ? 0 : 1,
          mr: isSmallScreen ? 1 : 1,
          mb: isSmallScreen ? 1 : 1,
          border: `1px solid ${colors.border}`,
          borderRadius: '6px',
          backgroundColor: colors.paper,
          minWidth: isSmallScreen ? 'auto' : '150px',
          maxWidth: isSmallScreen ? '100%' : '150px',
          width: isSmallScreen ? '100%' : '150px',
          flex: isSmallScreen ? '1 1 auto' : '0 0 150px',
          alignSelf: isSmallScreen ? 'stretch' : 'flex-start',
          maxHeight: isSmallScreen ? 'auto' : 'calc(100% - 16px)',
          overflow: 'hidden',
          display: 'flex',
          flexDirection: 'column',
        }}>
        <Typography
          variant='subtitle2'
          fontWeight='500'
          sx={{ mb: 1, color: colors.textPrimary }}>
          Legend
        </Typography>

        {renderCohortLegendItems()}

        <Divider sx={{ my: 0.75, backgroundColor: colors.border }} />

        <Box sx={{ pt: 0.5 }}>
          <Box sx={{ display: 'flex', alignItems: 'center', mb: 0.75 }}>
            <Box
              sx={{
                width: 10,
                height: 10,
                display: 'flex',
                justifyContent: 'center',
                alignItems: 'center',
                mr: 0.75,
                flexShrink: 0,
              }}>
              <Box
                component='hr'
                sx={{
                  width: 15,
                  height: 2,
                  backgroundColor: colors.tipNode,
                  border: 'none',
                }}
              />
            </Box>
            <Typography variant='caption' sx={{ color: colors.textPrimary }}>
              High-work path
            </Typography>
          </Box>

          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <Box
              sx={{
                width: 10,
                height: 10,
                borderRadius: '50%',
                backgroundColor: colorScale('0'),
                border: `2px solid ${colors.tipNode}`,
                mr: 0.75,
                flexShrink: 0,
              }}
            />
            <Typography variant='caption' sx={{ color: colors.textPrimary }}>
              Tip nodes
            </Typography>
          </Box>
        </Box>
      </Paper>
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
