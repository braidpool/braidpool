import React from 'react';
import { render, screen } from '@testing-library/react';
import AdvancedChart from '../AdvancedChart';
import { AdvancedchartProps } from '../lib/Types';

const renderWithSize = (ui: React.ReactElement) =>
  render(<div style={{ width: '800px', height: '500px' }}>{ui}</div>);

const mockData: AdvancedchartProps['data'] = [
  { timestamp: Date.now() - 2000, value: 10.123 },
  { timestamp: Date.now() - 1000, value: 20.456 },
  { timestamp: Date.now(), value: 30.789 },
];

beforeAll(() => {
  global.ResizeObserver = class {
    observe() {}
    unobserve() {}
    disconnect() {}
  };

  Object.defineProperty(HTMLElement.prototype, 'offsetHeight', {
    configurable: true,
    value: 500,
  });
  Object.defineProperty(HTMLElement.prototype, 'offsetWidth', {
    configurable: true,
    value: 800,
  });
  Object.defineProperty(HTMLElement.prototype, 'getBoundingClientRect', {
    configurable: true,
    value: () => ({
      width: 800,
      height: 500,
      top: 0,
      left: 0,
      bottom: 500,
      right: 800,
      x: 0,
      y: 0,
      toJSON: () => {},
    }),
  });
});

jest.mock('recharts', () => {
  const ActualRecharts = jest.requireActual('recharts');
  return {
    ...ActualRecharts,
    ResponsiveContainer: ({ children }: any) => (
      <div data-testid="responsive-container">{children}</div>
    ),
    LineChart: ({ children, data }: any) => (
      <svg data-testid="line-chart" data-chart-data={JSON.stringify(data)}>
        {children}
      </svg>
    ),
    YAxis: ({ unit, tick }: any) => (
      <g
        data-testid="y-axis"
        data-unit={unit}
        data-tick={JSON.stringify(tick)}
      />
    ),
    Line: ({ stroke, strokeWidth, dot, type, dataKey }: any) => (
      <g
        data-testid="line"
        data-stroke={stroke}
        data-stroke-width={strokeWidth}
        data-dot={dot}
        data-type={type}
        data-datakey={dataKey}
      />
    ),
    XAxis: ({ tickFormatter, tick, domain, type, scale, dataKey }: any) => {
      const mockTimestamp = Date.now();
      const formattedValue = tickFormatter ? tickFormatter(mockTimestamp) : '';
      return (
        <g
          data-testid="x-axis"
          data-formatted-time={formattedValue}
          data-tick={JSON.stringify(tick)}
          data-domain={JSON.stringify(domain)}
          data-type={type}
          data-scale={scale}
          data-datakey={dataKey}
        />
      );
    },
    Tooltip: ({ contentStyle, labelFormatter, formatter }: any) => {
      const mockTimestamp = Date.now();
      const mockValue = 25.123;
      const labelFormatted = labelFormatter
        ? labelFormatter(mockTimestamp)
        : '';
      const valueFormatted = formatter ? formatter(mockValue) : '';
      return (
        <g
          data-testid="tooltip"
          data-content-style={JSON.stringify(contentStyle)}
          data-label-formatted={labelFormatted}
          data-value-formatted={JSON.stringify(valueFormatted)}
        />
      );
    },
    CartesianGrid: ({ stroke }: any) => (
      <g data-testid="cartesian-grid" data-stroke={stroke} />
    ),
    Legend: () => <g data-testid="legend" />,
  };
});

describe('<AdvancedChart />', () => {
  it('renders SVG chart with valid data', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    const svg = document.querySelector('svg');
    expect(svg).toBeInTheDocument();
  });

  it('renders without crashing on empty data', () => {
    renderWithSize(<AdvancedChart data={[]} yLabel="Latency" unit="ms" />);
    const svg = document.querySelector('svg');
    expect(svg).toBeInTheDocument();
  });

  it('renders chart container', () => {
    const { getByTestId } = renderWithSize(
      <AdvancedChart data={mockData} yLabel="Hashrate" unit="EH/s" />
    );
    expect(getByTestId('responsive-container')).toBeInTheDocument();
    expect(getByTestId('line-chart')).toBeInTheDocument();
  });

  it('renders the line path for data', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    expect(screen.getByTestId('line')).toBeInTheDocument();
  });

  it('does not render dots on the line chart', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Speed" unit="ms" />);
    const line = screen.getByTestId('line');
    expect(line.getAttribute('data-dot')).toBe('false');
  });

  it('renders the tooltip container', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    expect(screen.getByTestId('tooltip')).toBeInTheDocument();
  });

  it('renders Y-axis with unit', () => {
    const { getByTestId } = renderWithSize(
      <AdvancedChart data={mockData} yLabel="Rate" unit="GB/s" />
    );
    const yAxis = getByTestId('y-axis');
    expect(yAxis).toBeInTheDocument();
    expect(yAxis.getAttribute('data-unit')).toBe(' GB/s');
  });

  it('applies custom line color', () => {
    const customColor = '#ff0000';
    renderWithSize(
      <AdvancedChart
        data={mockData}
        yLabel="Latency"
        unit="ms"
        lineColor={customColor}
      />
    );
    const line = screen.getByTestId('line');
    expect(line.getAttribute('data-stroke')).toBe(customColor);
  });

  it('applies default line color when not specified', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    const line = screen.getByTestId('line');
    expect(line.getAttribute('data-stroke')).toBe('#3b82f6');
  });

  it('handles data with missing values gracefully', () => {
    const brokenData = [
      { timestamp: Date.now() - 2000 },
      { value: 100 },
      { timestamp: 'invalid', value: 200 },
    ] as any;

    renderWithSize(
      <AdvancedChart data={brokenData} yLabel="Broken" unit="%" />
    );
    const svg = document.querySelector('svg');
    expect(svg).toBeInTheDocument();
  });

  it('configures Line component with correct properties', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    const line = screen.getByTestId('line');

    expect(line.getAttribute('data-type')).toBe('monotone');
    expect(line.getAttribute('data-datakey')).toBe('value');
    expect(line.getAttribute('data-stroke-width')).toBe('2');
    expect(line.getAttribute('data-dot')).toBe('false');
  });

  it('configures XAxis with correct properties', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    const xAxis = screen.getByTestId('x-axis');

    expect(xAxis.getAttribute('data-datakey')).toBe('timestamp');
    expect(xAxis.getAttribute('data-type')).toBe('number');
    expect(xAxis.getAttribute('data-scale')).toBe('time');
    expect(xAxis.getAttribute('data-domain')).toBe('["auto","auto"]');
  });

  it('configures CartesianGrid with correct stroke color', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    const grid = screen.getByTestId('cartesian-grid');
    expect(grid.getAttribute('data-stroke')).toBe('#444');
  });

  it('passes data correctly to LineChart', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Latency" unit="ms" />
    );
    const lineChart = screen.getByTestId('line-chart');
    const chartData = JSON.parse(
      lineChart.getAttribute('data-chart-data') || '[]'
    );
    expect(chartData).toEqual(mockData);
  });

  it('formats tooltip values with correct precision and unit', () => {
    renderWithSize(
      <AdvancedChart data={mockData} yLabel="Speed" unit="MB/s" />
    );
    const tooltip = screen.getByTestId('tooltip');

    const valueFormatted = JSON.parse(
      tooltip.getAttribute('data-value-formatted') || '[]'
    );
    expect(valueFormatted[0]).toBe('25.12 MB/s'); // Should be formatted to 2 decimal places
    expect(valueFormatted[1]).toBe('Speed'); // Should use the yLabel
  });
});
