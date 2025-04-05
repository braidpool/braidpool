import React, { useEffect, useRef } from 'react';
import { Box, Typography, useTheme } from '@mui/material';
import * as d3 from 'd3';
import colors from '../theme/colors';
import Card from './common/Card';

// Mock data for the hashrate over time
const hashrateData = [
  { time: '43m', value: 68.2 },
  { time: '40m', value: 72.5 },
  { time: '36m', value: 93.1 },
  { time: '32m', value: 86.7 },
  { time: '28m', value: 79.5 },
  { time: '24m', value: 84.8 },
  { time: '23m', value: 89.2 },
  { time: '22m', value: 98.3 },
];

interface PoolHashrateChartProps {
  height?: number;
}

const PoolHashrateChart: React.FC<PoolHashrateChartProps> = ({
  height = 300,
}) => {
  const chartRef = useRef<SVGSVGElement>(null);
  const theme = useTheme();

  useEffect(() => {
    if (!chartRef.current) return;

    // Clear previous content
    d3.select(chartRef.current).selectAll('*').remove();

    // Set up dimensions and margins
    const margin = { top: 30, right: 30, bottom: 50, left: 60 };
    const width = chartRef.current.clientWidth - margin.left - margin.right;
    const chartHeight = height - margin.top - margin.bottom;

    // Create SVG
    const svg = d3
      .select(chartRef.current)
      .attr('width', width + margin.left + margin.right)
      .attr('height', height)
      .append('g')
      .attr('transform', `translate(${margin.left},${margin.top})`);

    // Set up scales
    const x = d3
      .scaleBand()
      .domain(hashrateData.map((d) => d.time))
      .range([0, width])
      .padding(0.1);

    const y = d3
      .scaleLinear()
      .domain([0, 100]) // Fixed y-axis from 0 to 100
      .range([chartHeight, 0]);

    // Add the X axis
    svg
      .append('g')
      .attr('transform', `translate(0,${chartHeight})`)
      .call(d3.axisBottom(x))
      .selectAll('text')
      .style('fill', colors.textSecondary)
      .style('font-size', '12px');

    // Add the Y axis
    svg
      .append('g')
      .call(
        d3
          .axisLeft(y)
          .tickValues([0, 20, 40, 60, 80, 100])
          .tickFormat((d) => `${d}`)
      )
      .selectAll('text')
      .style('fill', colors.textSecondary)
      .style('font-size', '12px');

    // Add grid lines
    svg
      .append('g')
      .attr('class', 'grid')
      .selectAll('line')
      .data([0, 20, 40, 60, 80, 100])
      .enter()
      .append('line')
      .attr('x1', 0)
      .attr('x2', width)
      .attr('y1', (d) => y(d))
      .attr('y2', (d) => y(d))
      .attr('stroke', colors.chartGrid)
      .attr('stroke-dasharray', '3,3');

    // Create line generator
    const line = d3
      .line<{ time: string; value: number }>()
      .x((d) => x(d.time)! + x.bandwidth() / 2)
      .y((d) => y(d.value))
      .curve(d3.curveMonotoneX);

    // Add the line path
    svg
      .append('path')
      .datum(hashrateData)
      .attr('fill', 'none')
      .attr('stroke', colors.chartLine)
      .attr('stroke-width', 2.5)
      .attr('d', line);

    // Add data points
    svg
      .selectAll('.dot')
      .data(hashrateData)
      .enter()
      .append('circle')
      .attr('class', 'dot')
      .attr('cx', (d) => x(d.time)! + x.bandwidth() / 2)
      .attr('cy', (d) => y(d.value))
      .attr('r', 4)
      .attr('fill', colors.chartLine)
      .attr('stroke', colors.chartBackground)
      .attr('stroke-width', 2);

    // Add y-axis label
    svg
      .append('text')
      .attr('transform', 'rotate(-90)')
      .attr('y', -margin.left + 15)
      .attr('x', -chartHeight / 2)
      .attr('text-anchor', 'middle')
      .style('fill', colors.textSecondary)
      .text('PH/s');

    // Add x-axis label
    svg
      .append('text')
      .attr('y', chartHeight + margin.bottom - 10)
      .attr('x', width / 2)
      .attr('text-anchor', 'middle')
      .style('fill', colors.textSecondary)
      .text('Time');

    // Print debug info
    console.log('🔄 Pool hashrate chart rendered');
  }, [height]);

  return (
    <Card
      title='Pool Hashrate'
      subtitle='Live network performance over time'
      accentColor={colors.cardAccentPrimary}>
      <Box
        sx={{
          width: '100%',
          height: height,
          overflow: 'hidden',
        }}>
        <svg ref={chartRef} style={{ width: '100%', height: '100%' }} />
      </Box>
    </Card>
  );
};

export default PoolHashrateChart;
