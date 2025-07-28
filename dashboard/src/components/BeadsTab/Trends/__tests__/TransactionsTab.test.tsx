import { render, screen, act, cleanup } from '@testing-library/react';
import LatencyTab from '../LatencyTab';
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

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const timestamp = new Date().toISOString();

    const fakeData = {
      type: 'latency_data',
      data: {
        averageLatency: 42.5,
        peakLatency: 88,
        peerCount: 7,
        validPings: 5,
        timestamp,
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(fakeData) });
    });

    expect(await screen.findByTestId('animated-stat')).toBeInTheDocument();
    expect(screen.getByText(/Average Latency: 43ms/)).toBeInTheDocument();
    expect(screen.getByText(/Peak Latency: 88ms/)).toBeInTheDocument();
    expect(screen.getByText(/Active Peers: 5\/7/)).toBeInTheDocument();
    expect(screen.getByTestId('advanced-chart')).toBeInTheDocument();
  });

  it('does not update UI if duplicate timestamp is received', async () => {
    const now = new Date();
    const timestamp = now.toISOString();
    const parsed = now.getTime();

    render(<LatencyTab timeRange="24h" />);

    // first message
    act(() => {
      wsInstances[0].onmessage({
        data: JSON.stringify({
          type: 'latency_data',
          data: {
            averageLatency: 40,
            peakLatency: 90,
            peerCount: 8,
            validPings: 6,
            timestamp,
          },
        }),
      });
    });

    // duplicate message
    act(() => {
      wsInstances[0].onmessage({
        data: JSON.stringify({
          type: 'latency_data',
          data: {
            averageLatency: 99,
            peakLatency: 999,
            peerCount: 1,
            validPings: 1,
            timestamp,
          },
        }),
      });
    });

    // still shows first data
    expect(
      await screen.findByText(/Average Latency: 40ms/)
    ).toBeInTheDocument();
    expect(screen.queryByText(/Average Latency: 99ms/)).not.toBeInTheDocument();
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
