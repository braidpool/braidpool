import { render, screen, act, cleanup } from '@testing-library/react';
import HashrateTab from '../HashrateTab';
import { beforeEach, describe, it } from '@jest/globals';
import '@testing-library/jest-dom';
global.WebSocket = require('ws');

jest.mock('../../AdvancedChart', () => () => (
  <div data-testid="advanced-chart" />
));
jest.mock('../../AnimatedStatCard', () => ({ title, value }: any) => (
  <div data-testid="animated-stat">{`${title}: ${value}`}</div>
));

describe('<HashrateTab />', () => {
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
        setTimeout(() => this.onopen?.(), 10); // simulate open after mount
      }

      send() {}
    } as any;
  });

  afterEach(() => {
    wsInstances = [];
    cleanup();
    jest.clearAllMocks();
  });

  it('renders loading initially', async () => {
    render(<HashrateTab timeRange="24h" />);
    expect(screen.getByText(/Loading hashrate data/i)).toBeInTheDocument();
  });

  it('handles websocket open and updates UI on receiving data', async () => {
    jest.useFakeTimers();

    render(<HashrateTab timeRange="24h" />);

    // Simulate WebSocket message
    const fakeData = {
      type: 'hashrate_data',
      data: {
        hashrate: 10,
        timestamp: new Date().toISOString(),
        networkDifficulty: 123456789,
      },
    };

    // Let the onopen fire
    act(() => {
      jest.advanceTimersByTime(10);
    });

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(fakeData) });
    });

    expect(screen.getByText(/Current Hashrate/i)).toBeInTheDocument();
    expect(screen.getByText(/Peak Hashrate/i)).toBeInTheDocument();
    expect(screen.getByText(/Network Difficulty/i)).toBeInTheDocument();
  });

  it('should not update if timestamp is older than last entry', async () => {
    const now = new Date();
    const older = new Date(now.getTime() - 10000).toISOString();
    const newer = new Date(now.getTime()).toISOString();

    render(<HashrateTab timeRange="24h" />);

    act(() => {
      wsInstances[0].onmessage({
        data: JSON.stringify({
          type: 'hashrate_data',
          data: {
            hashrate: 10,
            timestamp: newer,
            networkDifficulty: 123,
          },
        }),
      });
    });

    act(() => {
      wsInstances[0].onmessage({
        data: JSON.stringify({
          type: 'hashrate_data',
          data: {
            hashrate: 20,
            timestamp: older,
            networkDifficulty: 456,
          },
        }),
      });
    });

    expect(await screen.findByText(/10.00 EH\/s/)).toBeInTheDocument(); // still old hashrate
  });

  it('handles websocket error gracefully', async () => {
    render(<HashrateTab timeRange="24h" />);

    act(() => {
      wsInstances[0].onerror(new Event('error'));
    });

    expect(
      await screen.findByText(/Loading hashrate data/i)
    ).toBeInTheDocument(); // still loading, connection failed
  });

  it('cleans up websocket on unmount', () => {
    const { unmount } = render(<HashrateTab timeRange="24h" />);
    const instance = wsInstances[0];

    unmount();

    expect(instance.close).toHaveBeenCalled();
    expect(instance.onmessage).toBeNull();
  });
});
