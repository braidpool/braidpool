import '@testing-library/jest-dom';
import React from 'react';
import { render, screen } from '@testing-library/react';
import BandwidthPanel from '../Bandwidth';
import { BandwidthHistoryPoint } from '../Types';

const mockFormatBytes = jest.fn((bytes: number) => `${bytes} B`);

jest.mock('../Utils', () => ({
  formatBytes: (bytes: number) => mockFormatBytes(bytes),
}));

jest.mock('recharts', () => ({
  LineChart: ({ children }: { children: React.ReactNode }) => (
    <div data-testid="linechart">{children}</div>
  ),
  Line: () => <div data-testid="line" />,
  XAxis: ({ tickFormatter }: { tickFormatter?: (ts: number) => string }) => {
    if (tickFormatter) tickFormatter(Date.now());
    return <div data-testid="xaxis" />;
  },
  YAxis: ({ tickFormatter }: { tickFormatter?: (v: number) => string }) => {
    if (tickFormatter) tickFormatter(1024);
    return <div data-testid="yaxis" />;
  },
  Tooltip: ({
    formatter,
    labelFormatter,
  }: {
    formatter?: (value: number, name: string) => [string, string];
    labelFormatter?: (ts: number) => string;
  }) => {
    if (formatter) formatter(2048, 'Bytes Sent');
    if (labelFormatter) labelFormatter(Date.now());
    return <div data-testid="tooltip" />;
  },
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
  beforeEach(() => {
    mockFormatBytes.mockClear();
  });

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

    expect(screen.getAllByTestId('line').length).toBeGreaterThan(0);
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

  it('calls formatBytes for Y-axis and tooltip values', () => {
    render(<BandwidthPanel bandwidthHistory={mockBandwidthHistory} />);

    // Expect it to have been called for both bytesrecv and bytessent
    expect(mockFormatBytes).toHaveBeenCalledWith(1024);
    expect(mockFormatBytes).toHaveBeenCalledWith(2048);
  });
});
