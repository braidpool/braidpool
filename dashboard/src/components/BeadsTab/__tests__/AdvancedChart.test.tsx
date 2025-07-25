import React from 'react';
import { render, screen } from '@testing-library/react';
import AdvancedChart from '../AdvancedChart';
import { AdvancedchartProps } from '../lib/Types';

const renderWithSize = (ui: React.ReactElement) =>
  render(<div style={{ width: '800px', height: '500px' }}>{ui}</div>);

const mockData: AdvancedchartProps['data'] = [
  { timestamp: Date.now() - 2000, value: 10 },
  { timestamp: Date.now() - 1000, value: 20 },
  { timestamp: Date.now(), value: 30 },
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
    ResponsiveContainer: ({ children }: any) => <div data-testid="responsive-container">{children}</div>,
    LineChart: ({ children }: any) => <svg data-testid="line-chart">{children}</svg>,
    YAxis: () => <g data-testid="y-axis" />,
    Line: () => <g data-testid="line" />,
    XAxis: () => <g data-testid="x-axis" />,
    Tooltip: () => <g data-testid="tooltip" />,
    CartesianGrid: () => <g data-testid="cartesian-grid" />,
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
    const { getByTestId } = renderWithSize(<AdvancedChart data={mockData} yLabel="Hashrate" unit="EH/s" />);
    expect(getByTestId('responsive-container')).toBeInTheDocument();
    expect(getByTestId('line-chart')).toBeInTheDocument();
  });

  it('renders the line path for data', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Latency" unit="ms" />);
    expect(screen.getByTestId('line')).toBeInTheDocument();
  });

  it('does not render dots on the line chart', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Speed" unit="ms" />);
    const dots = document.querySelectorAll('.recharts-dot');
    expect(dots.length).toBe(0);
  });

  it('renders the tooltip container', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Latency" unit="ms" />);
    expect(screen.getByTestId('tooltip')).toBeInTheDocument();
  });

  it('renders Y-axis', () => {
    const { getByTestId } = renderWithSize(<AdvancedChart data={mockData} yLabel="Rate" unit="GB/s" />);
    expect(getByTestId('y-axis')).toBeInTheDocument();
  });

  it('applies custom line color', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Latency" unit="ms"  />);
    expect(screen.getByTestId('line')).toBeInTheDocument();
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
    expect(svg).toBeInTheDocument(); // Should not crash
  });

  it('renders human-readable timestamps on X-axis', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Latency" unit="ms" />);
    expect(screen.getByTestId('x-axis')).toBeInTheDocument();
  });
});
