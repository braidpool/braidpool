import { render, screen, act, cleanup } from '@testing-library/react';
import LatencyTab from '../LatencyTab';
import { beforeEach, describe, it, afterEach } from '@jest/globals';

global.WebSocket = require('ws');

import '@testing-library/jest-dom';

jest.mock('../../AdvancedChart', () => () => (
  <div data-testid="advanced-chart">Chart</div>
));

jest.mock('../../AnimatedStatCard', () => ({ title, value }: any) => (
  <div data-testid="animated-stat">{`${title}: ${value}`}</div>
));

describe('<LatencyTab />', () => {
  let wsInstances: any[] = [];

  beforeEach(() => {
    global.WebSocket = class {
      static OPEN = 1;
      readyState = WebSocket.OPEN;
      onopen: (() => void) | null = null;
      onclose: (() => void) | null = null;
      onmessage: ((event: any) => void) | null = null;
      onerror: ((event: any) => void) | null = null;
      close = jest.fn();

      constructor() {
        wsInstances.push(this);
        setTimeout(() => this.onopen?.(), 10); // simulate opening
      }

      send() {}
    } as any;
  });

  afterEach(() => {
    wsInstances = [];
    cleanup();
    jest.clearAllMocks();
  });

  it('renders loading initially', () => {
    render(<LatencyTab timeRange="24h" />);
    expect(screen.getByText(/Loading latency data/i)).toBeInTheDocument();
  });

  it('handles websocket open and renders data on receiving message', async () => {
    jest.useFakeTimers();

    render(<LatencyTab timeRange="24h" />);

    const fakeData = {
      type: 'latency_data',
      data: {
        averageLatency: 42.5,
        peakLatency: 88,
        peerCount: 7,
        validPings: 5,
        timestamp: new Date().toISOString(),
      },
    };

    act(() => {
      jest.advanceTimersByTime(10);
    });

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(fakeData) });
    });

    expect(screen.getByText(/Average Latency: 43ms/)).toBeInTheDocument();
    expect(screen.getByText(/Peak Latency: 88ms/)).toBeInTheDocument();
    expect(screen.getByText(/Active Peers: 5\/7/)).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('does not update UI if duplicate timestamp is received', async () => {
    jest.useFakeTimers();

    const timestamp = new Date('2024-01-01T10:00:00.000Z').toISOString();

    render(<LatencyTab timeRange="24h" />);

    act(() => {
      jest.advanceTimersByTime(10);
    });

    const firstMessage = {
      type: 'latency_data',
      data: {
        averageLatency: 40,
        peakLatency: 90,
        peerCount: 8,
        validPings: 6,
        timestamp,
      },
    };

    const secondMessage = {
      type: 'latency_data',
      data: {
        averageLatency: 99,
        peakLatency: 999,
        peerCount: 1,
        validPings: 1,
        timestamp,
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(firstMessage) });
    });

    expect(screen.getByText(/Average Latency: 40ms/)).toBeInTheDocument();
    expect(screen.getByText(/Peak Latency: 90ms/)).toBeInTheDocument();
    expect(screen.getByText(/Active Peers: 6\/8/)).toBeInTheDocument();
    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(secondMessage) });
    });

    expect(screen.getByText(/Average Latency: 99ms/)).toBeInTheDocument();
    expect(screen.getByText(/Peak Latency: 999ms/)).toBeInTheDocument();
    expect(screen.getByText(/Active Peers: 1\/1/)).toBeInTheDocument();

    expect(screen.queryByText(/Average Latency: 40ms/)).not.toBeInTheDocument();
    expect(screen.queryByText(/Peak Latency: 90ms/)).not.toBeInTheDocument();
    expect(screen.queryByText(/Active Peers: 6\/8/)).not.toBeInTheDocument();

    jest.useRealTimers();
  });

  it('handles websocket error and shows fallback', async () => {
    render(<LatencyTab timeRange="24h" />);

    act(() => {
      wsInstances[0].onerror(new Event('error'));
    });

    expect(
      await screen.findByText(/Loading latency data/i)
    ).toBeInTheDocument();
  });

  it('cleans up websocket connection on unmount', () => {
    const { unmount } = render(<LatencyTab timeRange="24h" />);
    const ws = wsInstances[0];

    unmount();

    expect(ws.close).toHaveBeenCalled();
    expect(ws.onmessage).toBeNull();
    expect(ws.onopen).toBeNull();
    expect(ws.onclose).toBeNull();
    expect(ws.onerror).toBeNull();
  });
});
