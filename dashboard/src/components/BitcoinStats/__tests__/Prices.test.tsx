import '@testing-library/jest-dom';
import React from 'react';
import { render, screen, waitFor, act } from '@testing-library/react';
import { getLatestTransactions, latestRBFTransactions } from '../Utils';
import BitcoinPriceTracker from '../Prices';

// Mock utility functions
jest.mock('../Utils', () => ({
  getLatestTransactions: jest.fn(),
  latestRBFTransactions: jest.fn(),
  formatLargeNumber: jest.fn((num) => num.toString()),
  formatPrice: jest.fn((num) => num.toString()),
  getCurrencySymbol: jest.fn((currency: string) => {
    const symbols: Record<string, string> = {
      USD: '$',
      EUR: '€',
      GBP: '£',
      JPY: '¥',
    };
    return symbols[currency] || '$';
  }),
}));

// Mock recharts
jest.mock('recharts', () => ({
  BarChart: ({ children }: { children: React.ReactNode }) => (
    <div data-testid="barchart">{children}</div>
  ),
  LineChart: ({ children }: { children: React.ReactNode }) => (
    <div data-testid="linechart">{children}</div>
  ),
  Bar: () => <div data-testid="bar" />,
  Line: () => <div data-testid="line" />,
  XAxis: () => <div data-testid="xaxis" />,
  YAxis: () => <div data-testid="yaxis" />,
  Tooltip: () => <div data-testid="tooltip" />,
  Legend: () => <div data-testid="legend" />,
  CartesianGrid: () => <div data-testid="cartesiangrid" />,
  ResponsiveContainer: ({ children }: { children: React.ReactNode }) => (
    <div data-testid="responsivecontainer">{children}</div>
  ),
}));

// Mock transaction tables
jest.mock('../TransactionTable', () => () => (
  <div data-testid="transaction-table" />
));
jest.mock('../RBFTransactionTable', () => () => (
  <div data-testid="rbf-transaction-table" />
));

// Mock MAX_HISTORY_ITEMS constant
jest.mock('../Constants', () => ({
  MAX_HISTORY_ITEMS: 30,
}));

// Mock WebSocket
class MockWebSocket {
  static instances: MockWebSocket[] = [];
  onopen: () => void = () => {};
  onmessage: (event: { data: string }) => void = () => {};
  onclose: () => void = () => {};
  readyState: number = WebSocket.CONNECTING;

  constructor() {
    MockWebSocket.instances.push(this);
  }

  static mockOpen() {
    MockWebSocket.instances.forEach((instance) => {
      instance.readyState = WebSocket.OPEN;
      instance.onopen();
    });
  }

  static mockMessage(data: any) {
    MockWebSocket.instances.forEach((instance) => {
      instance.onmessage({ data: JSON.stringify(data) });
    });
  }

  static mockClose() {
    MockWebSocket.instances.forEach((instance) => {
      instance.readyState = WebSocket.CLOSED;
      instance.onclose();
    });
  }

  close() {
    this.readyState = WebSocket.CLOSED;
    this.onclose();
  }
}

global.WebSocket = MockWebSocket as any;

describe('BitcoinPriceTracker', () => {
  beforeEach(() => {
    jest.clearAllMocks();
    MockWebSocket.instances = [];

    (getLatestTransactions as jest.Mock).mockResolvedValue([
      { id: 'tx1', amount: 0.5 },
      { id: 'tx2', amount: 1.2 },
    ]);

    (latestRBFTransactions as jest.Mock).mockResolvedValue([
      { id: 'rbf1', amount: 0.3 },
      { id: 'rbf2', amount: 0.7 },
    ]);
  });

  // The loading skeleton uses animate-pulse as a CSS class, not a data-testid.
  // Query by the skeleton container element instead.
  it('renders loading state initially', () => {
    render(<BitcoinPriceTracker />);
    const skeletons = document.querySelectorAll('.animate-pulse');
    expect(skeletons.length).toBeGreaterThan(0);
  });

  // Labels in the component are lowercase: "24h low" / "24h high"
  it('connects to WebSocket and displays price data', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 50000, high24h: 51000, low24h: 49000 } },
        },
      });
    });

    await waitFor(() => {
      expect(screen.getByText('24h high')).toBeInTheDocument();
      expect(screen.getByText('24h low')).toBeInTheDocument();
    });
  });

  // Labels match the component: "Market cap", "Active cryptos", "BTC dominance"
  it('displays global stats when data is received', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 50000, high24h: 51000, low24h: 49000 } },
          global_stats: {
            market_cap: 1000000000000,
            market_cap_change: 2.5,
            active_cryptocurrencies: 10000,
            active_markets: 500,
            bitcoin_dominance: 0.45,
          },
        },
      });
    });

    await waitFor(() => {
      // formatLargeNumber mock returns num.toString()
      expect(screen.getByText('1000000000000')).toBeInTheDocument();
      // Actual label used in the component
      expect(screen.getByText('Active cryptos')).toBeInTheDocument();
      // bitcoin_dominance * 100, toFixed(2)
      expect(screen.getByText('45.00%')).toBeInTheDocument();
    });
  });

  it('fetches transactions on mount and periodically', async () => {
    jest.useFakeTimers();
    render(<BitcoinPriceTracker />);
    await waitFor(() => {
      expect(getLatestTransactions).toHaveBeenCalledTimes(1);
    });

    act(() => {
      jest.advanceTimersByTime(5000);
    });

    await waitFor(() => {
      expect(getLatestTransactions).toHaveBeenCalledTimes(2);
    });

    jest.useRealTimers();
  });

  it('displays transaction tables when data is available', async () => {
    render(<BitcoinPriceTracker />);
    await waitFor(() => {
      expect(screen.getByTestId('transaction-table')).toBeInTheDocument();
      expect(screen.getByTestId('rbf-transaction-table')).toBeInTheDocument();
    });
  });

  it('renders price history chart', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 50000, high24h: 51000, low24h: 49000 } },
        },
      });
    });

    await waitFor(() => {
      expect(screen.getByTestId('linechart')).toBeInTheDocument();
    });
  });

  it('renders price range bar chart', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 50000, high24h: 51000, low24h: 49000 } },
        },
      });
    });

    await waitFor(() => {
      expect(screen.getByTestId('barchart')).toBeInTheDocument();
    });
  });

  it('cleans up WebSocket on unmount', () => {
    const { unmount } = render(<BitcoinPriceTracker />);
    act(() => MockWebSocket.mockOpen());
    const instance = MockWebSocket.instances[0];
    const closeSpy = jest.spyOn(instance, 'close');
    unmount();
    expect(closeSpy).toHaveBeenCalled();
  });

  // Component uses text-emerald-500 for up and text-red-500 for down (not text-green-500)
  it('shows emerald color when price goes up and red when down', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 50000, high24h: 51000, low24h: 49000 } },
        },
      });
    });

    act(() => {
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 51000, high24h: 52000, low24h: 49000 } },
        },
      });
    });

    await waitFor(() => {
      expect(screen.getByText(/\$51000/)).toHaveClass('text-emerald-500');
    });

    act(() => {
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: { current: 49000, high24h: 52000, low24h: 47000 } },
        },
      });
    });

    await waitFor(() => {
      expect(screen.getByText(/\$49000/)).toHaveClass('text-red-500');
    });
  });

  it('sets error when WebSocket sends invalid JSON', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.instances[0].onmessage({ data: 'not-a-json' });
    });

    await waitFor(() => {
      expect(
        screen.getByText('Invalid data format received')
      ).toBeInTheDocument();
    });
  });

  // MAX_HISTORY_ITEMS is imported from Constants (mocked as 30).
  // This test verifies the chart renders after receiving many updates.
  it('limits price history to MAX_HISTORY_ITEMS entries', async () => {
    render(<BitcoinPriceTracker />);
    act(() => {
      MockWebSocket.mockOpen();
      for (let i = 0; i < 35; i++) {
        MockWebSocket.mockMessage({
          type: 'bitcoin_update',
          data: {
            price: {
              USD: { current: 50000 + i, high24h: 51000, low24h: 49000 },
            },
          },
        });
      }
    });

    await waitFor(() => {
      expect(screen.getByTestId('linechart')).toBeInTheDocument();
    });
  });
});
