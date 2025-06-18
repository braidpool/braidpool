import '@testing-library/jest-dom';
import React from 'react';
import { render, screen, waitFor, act } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import BitcoinPriceTracker from '../Prices';
import { getLatestTransactions, latestRBFTransactions } from '../Utils';

// Mock the WebSocket and utility functions
jest.mock('../Utils', () => ({
  getLatestTransactions: jest.fn(),
  latestRBFTransactions: jest.fn(),
  formatLargeNumber: jest.fn((num) => num.toString()),
  formatPrice: jest.fn((num) => num.toString()),
  getCurrencySymbol: jest.fn((currency: string) => {
    const symbols: Record<string, string> = { USD: '$', EUR: '€', GBP: '£', JPY: '¥' };
    return symbols[currency] || '$';
  }),
}));

// Mock the recharts components to simplify testing
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

// Mock the TransactionTable components
jest.mock('../TransactionTable', () => () => (
  <div data-testid="transaction-table" />
));
jest.mock('../RBFTransactions', () => () => (
  <div data-testid="rbf-transaction-table" />
));

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

  it('renders loading state initially', () => {
    render(<BitcoinPriceTracker />);
    expect(screen.getAllByTestId('animate-pulse').length).toBeGreaterThan(0);
  });

  it('connects to WebSocket and displays price data', async () => {
    render(<BitcoinPriceTracker />);
    
    // Simulate WebSocket connection and message
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: 50000, EUR: 45000, GBP: 40000, JPY: 5500000 },
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

    expect(screen.getByText('24H High')).toBeInTheDocument();
    expect(screen.getByText('24H Low')).toBeInTheDocument();
  });

  it('displays global stats when data is received', async () => {
    render(<BitcoinPriceTracker />);
    
    act(() => {
      MockWebSocket.mockOpen();
      MockWebSocket.mockMessage({
        type: 'bitcoin_update',
        data: {
          price: { USD: 50000 },
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
      expect(screen.getByText('1000000000000')).toBeInTheDocument();
      });
    
    expect(screen.getByText('Active Cryptocurrencies')).toBeInTheDocument();
    expect(screen.getByText('45.00%')).toBeInTheDocument();
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
        data: { price: { USD: 50000 } },
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
        data: { price: { USD: 50000 } },
      });
    });

    await waitFor(() => {
      expect(screen.getByTestId('barchart')).toBeInTheDocument();
    });
  });

  it('cleans up WebSocket on unmount', () => {
    const { unmount } = render(<BitcoinPriceTracker />);
    
    const instance = MockWebSocket.instances[0];
    const closeSpy = jest.spyOn(instance, 'close');
    
    unmount();
    
    expect(closeSpy).toHaveBeenCalled();
  });
});