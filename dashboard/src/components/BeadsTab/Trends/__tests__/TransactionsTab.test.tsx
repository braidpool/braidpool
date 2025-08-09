import { render, screen, act, cleanup } from '@testing-library/react';
import TransactionsTab from '../TransactionsTab';
import '@testing-library/jest-dom';

jest.mock('../../AdvancedChart', () => () => (
  <div data-testid="advanced-chart">Chart</div>
));
jest.mock('../../AnimatedStatCard', () => ({ title, value }: any) => (
  <div data-testid="animated-stat">{`${title}: ${value}`}</div>
));

describe('<TransactionsTab />', () => {
  let wsInstances: any[] = [];
  let mockSetChartHovered: jest.Mock;

  beforeEach(() => {
    mockSetChartHovered = jest.fn();
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

    // Mock console methods to suppress logs during tests
    jest.spyOn(console, 'error').mockImplementation(() => {});
    jest.spyOn(console, 'log').mockImplementation(() => {});
  });

  afterEach(() => {
    wsInstances = [];
    cleanup();
    jest.clearAllMocks();
    jest.restoreAllMocks();
  });

  it('renders loading state initially', () => {
    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    expect(screen.getByText('Transaction Activity')).toBeInTheDocument();
    expect(
      screen.getByText('Real-time transaction statistics')
    ).toBeInTheDocument();
    expect(screen.getByText('Loading...')).toBeInTheDocument();
  });

  it('handles websocket open and renders transaction stats', async () => {
    jest.useFakeTimers();

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const transactionStatsData = {
      type: 'transaction_stats',
      data: {
        txRate: 5.2,
        mempoolSize: 1500,
        avgFeeRate: 12.5,
        avgTxSize: 250,
        averagingWindow: 10,
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(transactionStatsData) });
    });

    // Check that loading state is replaced with actual data
    expect(screen.queryByText('Loading...')).not.toBeInTheDocument();
    expect(screen.getByText('5.2 tx/min')).toBeInTheDocument();
    expect(screen.getByText('Moving Avg (10 blocks)')).toBeInTheDocument();

    // Use findAllByTestId since there are multiple animated-stat elements
    expect(await screen.findAllByTestId('animated-stat')).toHaveLength(3);
    expect(screen.getByText(/Mempool Size: 1,500 tx/)).toBeInTheDocument();
    expect(screen.getByText(/Avg Fee Rate: 12.5 sat\/vB/)).toBeInTheDocument();
    expect(screen.getByText(/Avg Tx Size: 250 vB/)).toBeInTheDocument();
    expect(screen.getByTestId('advanced-chart')).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('handles block data and updates chart', async () => {
    jest.useFakeTimers();

    const mockDate = new Date('2024-01-01T10:00:00.000Z');
    jest.setSystemTime(mockDate);

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const blockData = {
      type: 'block_data',
      data: {
        txCount: 150,
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(blockData) });
    });

    expect(screen.getByTestId('advanced-chart')).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('does not add duplicate chart entries for same timestamp', async () => {
    jest.useFakeTimers();

    const mockDate = new Date('2024-01-01T10:00:00.000Z');
    jest.setSystemTime(mockDate);

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const firstBlockData = {
      type: 'block_data',
      data: {
        txCount: 100,
      },
    };

    const secondBlockData = {
      type: 'block_data',
      data: {
        txCount: 200,
      },
    };

    // Send first block data
    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(firstBlockData) });
    });

    // Send second block data with same timestamp (same system time)
    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(secondBlockData) });
    });

    // Chart should still be rendered (duplicate prevention is internal)
    expect(screen.getByTestId('advanced-chart')).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('handles websocket error and shows error state', async () => {
    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      wsInstances[0].onerror(new Event('error'));
    });

    expect(
      await screen.findByText(/Error: WebSocket connection error/)
    ).toBeInTheDocument();
    expect(screen.queryByText('Loading...')).not.toBeInTheDocument();
  });

  it('handles error messages from server', async () => {
    jest.useFakeTimers();

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const errorMessage = {
      type: 'error',
      data: {
        message: 'Server connection failed',
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(errorMessage) });
    });

    expect(
      screen.getByText(/Error: Server connection failed/)
    ).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('handles malformed JSON messages', async () => {
    jest.useFakeTimers();

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    act(() => {
      wsInstances[0].onmessage({ data: 'invalid json' });
    });

    expect(screen.getByText(/Error: Failed to parse data/)).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('shows disconnected state when connection is lost', async () => {
    jest.useFakeTimers();

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    act(() => {
      wsInstances[0].onclose();
    });

    expect(await screen.findByText('Disconnected')).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('displays no data when stats are empty', async () => {
    jest.useFakeTimers();

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const emptyStatsData = {
      type: 'transaction_stats',
      data: {
        txRate: 0,
        mempoolSize: 0,
        avgFeeRate: 0,
        avgTxSize: 0,
        averagingWindow: 0,
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(emptyStatsData) });
    });

    expect(screen.getByText('No data')).toBeInTheDocument();
    expect(screen.getByText('Moving Avg (0 blocks)')).toBeInTheDocument();

    jest.useRealTimers();
  });

  it('cleans up websocket connection on unmount', () => {
    const { unmount } = render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );
    const ws = wsInstances[0];

    unmount();

    expect(ws.close).toHaveBeenCalled();
    expect(ws.onmessage).toBeNull();
    expect(ws.onopen).toBeNull();
    expect(ws.onclose).toBeNull();
    expect(ws.onerror).toBeNull();
  });

  it('recreates websocket connection when timeRange changes', () => {
    const { rerender } = render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );
    const firstWs = wsInstances[0];

    rerender(
      <TransactionsTab
        timeRange="7d"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    expect(firstWs.close).toHaveBeenCalled();
    expect(wsInstances).toHaveLength(2); // New WebSocket instance created
  });

  it('handles transaction stats with missing data gracefully', async () => {
    jest.useFakeTimers();

    render(
      <TransactionsTab
        timeRange="24h"
        chartHovered={false}
        setChartHovered={mockSetChartHovered}
      />
    );

    act(() => {
      jest.advanceTimersByTime(10); // simulate ws.onopen
    });

    const partialStatsData = {
      type: 'transaction_stats',
      data: {
        txRate: 3.7,
        // Missing other fields
      },
    };

    act(() => {
      wsInstances[0].onmessage({ data: JSON.stringify(partialStatsData) });
    });

    expect(screen.getByText('3.7 tx/min')).toBeInTheDocument();
    expect(screen.getByText('Moving Avg (0 blocks)')).toBeInTheDocument();

    jest.useRealTimers();
  });
});
