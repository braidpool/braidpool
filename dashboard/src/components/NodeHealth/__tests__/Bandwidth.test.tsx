import '@testing-library/jest-dom';
import React from 'react';
import { render, screen } from '@testing-library/react';
import BandwidthPanel from '../Bandwidth';
import { BandwidthHistoryPoint } from '../Types';

jest.mock('../Utils', () => ({
  formatBytes: jest.fn((bytes: number) => `${bytes} B`),
}));

jest.mock('recharts', () => ({
  LineChart: ({ children }: { children: React.ReactNode }) => (
    <div data-testid="linechart">{children}</div>
  ),
  Line: () => <div data-testid="line" />,
  XAxis: () => <div data-testid="xaxis" />,
  YAxis: () => <div data-testid="yaxis" />,
  Tooltip: () => <div data-testid="tooltip" />,
  CartesianGrid: () => <div data-testid="grid" />,
  ResponsiveContainer: ({ children }: { children: React.ReactNode }) => (
    <div data-testid="container">{children}</div>
  ),
}));

const mockBandwidthHistory: BandwidthHistoryPoint[] = [
  {
    timestamp: Date.now(),
    totalbytesrecv: 1024,
    totalbytessent: 2048,
  },
];

describe('BandwidthPanel', () => {
  it('renders "No bandwidth data available" when no history is passed', () => {
    render(<BandwidthPanel bandwidthHistory={[]} />);
    expect(
      screen.getByText(/no bandwidth data available/i)
    ).toBeInTheDocument();
  });

  it('renders the chart when bandwidth history is passed', () => {
    render(<BandwidthPanel bandwidthHistory={mockBandwidthHistory} />);
    expect(screen.getByText(/real-time bandwidth usage/i)).toBeInTheDocument();
    expect(screen.getByTestId('linechart')).toBeInTheDocument();

    const lines = screen.getAllByTestId('line');
    expect(lines.length).toBeGreaterThan(0);

    expect(screen.getByTestId('xaxis')).toBeInTheDocument();
    expect(screen.getByTestId('yaxis')).toBeInTheDocument();
    expect(screen.getByTestId('tooltip')).toBeInTheDocument();
    expect(screen.getByTestId('grid')).toBeInTheDocument();
    expect(screen.getByTestId('container')).toBeInTheDocument();
  });

  it('renders both Lines: Bytes Sent and Bytes Received', () => {
    render(<BandwidthPanel bandwidthHistory={mockBandwidthHistory} />);
    const lines = screen.getAllByTestId('line');
    expect(lines.length).toBeGreaterThanOrEqual(2);
  });
});
