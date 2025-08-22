import { render, screen, waitFor, act } from '@testing-library/react';
import { RewardsDashboard } from '../RewardsDashboard';
import { RewardPoint } from '../../lib/Types';
import { WEBSOCKET_URLS } from '@/URLs';

jest.mock('../../lib/Utils', () => ({
  calculateRewardAnalytics: jest.fn((data) => ({
    avgBTC: 6.25,
    avgUSD: 250000,
    rewardsPerHour: {
      BTC: 37.5,
      USD: 1500000,
      blocks: 6,
    },
    rewardsPerWeek: {
      BTC: 6300,
      USD: 252000000,
      blocks: 1008,
    },
    rewardsPerMonth: {
      BTC: 27000,
      USD: 1080000000,
      blocks: 4320,
    },
  })),
}));

// Mock the StatCard component
jest.mock('../RewardStats', () => ({
  StatCard: jest.fn(({ title, btcValue, usdValue, blocks, timeframe }) => (
    <div data-testid={`stat-card-${title.toLowerCase().replace(/\s+/g, '-')}`}>
      <div>{title}</div>
      <div>BTC: {btcValue}</div>
      <div>USD: {usdValue}</div>
      {blocks && <div>Blocks: {blocks}</div>}
      {timeframe && <div>Timeframe: {timeframe}</div>}
    </div>
  )),
}));

jest.mock('recharts', () => ({
  ResponsiveContainer: ({ children }: any) => (
    <div data-testid="responsive-container">{children}</div>
  ),
  LineChart: ({ children, data }: any) => (
    <div data-testid="line-chart" data-chart-data={JSON.stringify(data)}>
      {children}
    </div>
  ),
  Line: ({ dataKey, stroke, name, yAxisId }: any) => (
    <div
      data-testid={`line-${dataKey}`}
      data-stroke={stroke}
      data-name={name}
      data-y-axis={yAxisId}
    />
  ),
  XAxis: ({ dataKey, stroke }: any) => (
    <div data-testid="x-axis" data-key={dataKey} data-stroke={stroke} />
  ),
  YAxis: ({ yAxisId, orientation, stroke, domain }: any) => (
    <div
      data-testid={`y-axis-${yAxisId}`}
      data-orientation={orientation}
      data-stroke={stroke}
      data-domain={JSON.stringify(domain)}
    />
  ),
  CartesianGrid: ({ strokeDasharray, stroke }: any) => (
    <div
      data-testid="cartesian-grid"
      data-stroke-dasharray={strokeDasharray}
      data-stroke={stroke}
    />
  ),
  Tooltip: ({ content }: any) => (
    <div data-testid="tooltip" data-has-custom-content={!!content} />
  ),
  Legend: () => <div data-testid="legend" />,
}));

// Mock WebSocket
class MockWebSocket {
  static CONNECTING = 0;
  static OPEN = 1;
  static CLOSING = 2;
  static CLOSED = 3;

  readyState = MockWebSocket.CONNECTING;
  onopen: ((event: Event) => void) | null = null;
  onclose: ((event: CloseEvent) => void) | null = null;
  onerror: ((event: Event) => void) | null = null;
  onmessage: ((event: MessageEvent) => void) | null = null;

  constructor(public url: string) {
    setTimeout(() => {
      this.readyState = MockWebSocket.OPEN;
      if (this.onopen) {
        this.onopen(new Event('open'));
      }
    }, 100);
  }

  close() {
    this.readyState = MockWebSocket.CLOSED;
    if (this.onclose) {
      this.onclose(new CloseEvent('close'));
    }
  }
  simulateMessage(data: any) {
    if (this.onmessage) {
      this.onmessage(
        new MessageEvent('message', {
          data: JSON.stringify(data),
        })
      );
    }
  }

  simulateError() {
    if (this.onerror) {
      this.onerror(new Event('error'));
    }
  }
}

global.WebSocket = MockWebSocket as any;
const mockConsoleLog = jest.spyOn(console, 'log').mockImplementation();
const mockConsoleError = jest.spyOn(console, 'error').mockImplementation();

describe('RewardsDashboard Component', () => {
  const mockRewardData: RewardPoint[] = [
    {
      height: 800000,
      timestamp: '2023-01-01T12:00:00Z',
      rewardBTC: 6.25,
      rewardUSD: 250000,
    },
  ];

  let mockWs: MockWebSocket;

  beforeEach(() => {
    jest.clearAllMocks();
    mockConsoleLog.mockClear();
    mockConsoleError.mockClear();

    global.WebSocket = jest.fn().mockImplementation((url) => {
      mockWs = new MockWebSocket(url);
      return mockWs;
    }) as any;
  });

  afterEach(() => {
    if (mockWs && mockWs.readyState === MockWebSocket.OPEN) {
      mockWs.close();
    }
  });

  describe('Initial Rendering', () => {
    test('renders component with initial state', () => {
      render(<RewardsDashboard />);

      expect(screen.getByText('Reward Analytics')).toBeInTheDocument();
      expect(screen.getByText('Block Rewards')).toBeInTheDocument();
      expect(
        screen.getByText('Waiting for reward data...')
      ).toBeInTheDocument();
      expect(screen.getByText('Waiting for block data...')).toBeInTheDocument();
    });

    test('shows loading states when no data', () => {
      render(<RewardsDashboard />);

      const loadingMessages = screen.getAllByText(/waiting for.*data\.\.\./i);
      expect(loadingMessages).toHaveLength(2);
    });

    test('displays correct block count in chart header', () => {
      render(<RewardsDashboard />);

      expect(screen.getByText('(0 blocks)')).toBeInTheDocument();
    });
  });

  describe('WebSocket Connection', () => {
    test('establishes WebSocket connection on mount', () => {
      render(<RewardsDashboard />);

      expect(global.WebSocket).toHaveBeenCalledWith(
        WEBSOCKET_URLS.MAIN_WEBSOCKET
      );
    });

    test('handles WebSocket errors', async () => {
      render(<RewardsDashboard />);

      await act(async () => {
        mockWs.simulateError();
      });

      expect(mockConsoleError).toHaveBeenCalledWith(
        'WebSocket error:',
        expect.any(Event)
      );
    });

    test('logs disconnection', async () => {
      render(<RewardsDashboard />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      await act(async () => {
        mockWs.close();
      });

      expect(mockConsoleLog).toHaveBeenCalledWith('WebSocket disconnected');
    });
  });

  describe('Data Processing', () => {
    test('processes reward update messages correctly', async () => {
      render(<RewardsDashboard />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      const rawData = [
        {
          height: '800000',
          timestamp: '2023-01-01T12:00:00Z',
          rewardBTC: '6.25',
          rewardUSD: '250000',
        },
      ];

      await act(async () => {
        mockWs.simulateMessage({
          type: 'reward_update',
          data: rawData,
        });
      });

      expect(screen.getByText('(1 blocks)')).toBeInTheDocument();
    });

    test('converts string values to numbers', async () => {
      const { calculateRewardAnalytics } = require('../../lib/Utils');

      render(<RewardsDashboard />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      const rawData = [
        {
          height: '800000',
          timestamp: '2023-01-01T12:00:00Z',
          rewardBTC: '6.25',
          rewardUSD: '250000',
        },
      ];

      await act(async () => {
        mockWs.simulateMessage({
          type: 'reward_update',
          data: rawData,
        });
      });

      expect(calculateRewardAnalytics).toHaveBeenCalledWith([
        {
          height: 800000,
          timestamp: '2023-01-01T12:00:00Z',
          rewardBTC: 6.25,
          rewardUSD: 250000,
        },
      ]);
    });

    test('handles non-array data with error logging', async () => {
      render(<RewardsDashboard />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      await act(async () => {
        mockWs.simulateMessage({
          type: 'reward_update',
          data: { invalid: 'data' },
        });
      });

      expect(mockConsoleError).toHaveBeenCalledWith(
        'Expected array but got:',
        'object',
        { invalid: 'data' }
      );
    });

    test('ignores non-reward_update messages', async () => {
      render(<RewardsDashboard />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      await act(async () => {
        mockWs.simulateMessage({
          type: 'other_update',
          data: mockRewardData,
        });
      });

      expect(screen.getByText('(0 blocks)')).toBeInTheDocument();
    });

    test('handles JSON parsing errors', async () => {
      render(<RewardsDashboard />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      await act(async () => {
        if (mockWs.onmessage) {
          mockWs.onmessage(
            new MessageEvent('message', {
              data: 'invalid json',
            })
          );
        }
      });

      expect(mockConsoleError).toHaveBeenCalledWith(
        'WebSocket JSON error:',
        expect.any(SyntaxError)
      );
    });
  });
});
