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

  it('renders correct number of Y axis ticks', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Speed" unit="ms" />);
    const ticks = document.querySelectorAll(
      '.recharts-yAxis .recharts-cartesian-axis-tick-value'
    );
    expect(ticks.length).toBeGreaterThan(0);
  });

  it('renders the line path for data', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Speed" unit="ms" />);
    const path = document.querySelectorAll('path.recharts-curve');
    expect(path.length).toBeGreaterThan(0);
  });

  it('does not render dots on the line chart', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Speed" unit="ms" />);
    const dots = document.querySelectorAll('.recharts-dot');
    expect(dots.length).toBe(0);
  });

  it('renders the tooltip container', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Ping" unit="ms" />);
    const tooltipWrapper = document.querySelector('.recharts-tooltip-wrapper');
    expect(tooltipWrapper).toBeTruthy();
  });

  it('renders Y-axis with unit label', () => {
    renderWithSize(<AdvancedChart data={mockData} yLabel="Rate" unit="GB/s" />);
    const axis = document.querySelector('.recharts-yAxis');
    expect(axis?.textContent).toMatch(/GB\/s/);
  });

  it('applies custom line color', () => {
    const customColor = '#f59e0b';
    renderWithSize(
      <AdvancedChart
        data={mockData}
        yLabel="Flow"
        unit="L/s"
        lineColor={customColor}
      />
    );
    const line = document.querySelector('path.recharts-curve');
    expect(line?.getAttribute('stroke')).toBe(customColor);
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
    renderWithSize(<AdvancedChart data={mockData} yLabel="Ping" unit="ms" />);
    const xAxisLabels = document.querySelectorAll(
      '.recharts-xAxis .recharts-cartesian-axis-tick-value'
    );
    expect(xAxisLabels.length).toBeGreaterThan(0);
    for (const label of xAxisLabels) {
      expect(label.textContent).toMatch(/\d{2}:\d{2}:\d{2}/); // HH:MM:SS format
    }
  });
});
