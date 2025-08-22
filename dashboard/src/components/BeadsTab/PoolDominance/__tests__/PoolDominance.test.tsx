import { render, screen, waitFor, act } from '@testing-library/react';
import { PoolDominance } from '../PoolDominance';
import { PoolData } from '../../lib/Types';
import { WEBSOCKET_URLS } from '@/URLs';

jest.mock('../../lib/Utils', () => ({
  formatWork: jest.fn((value) => ({
    value: '100.5',
    unit: 'TH/s',
  })),
  formatFeePercentage: jest.fn((value) =>
    typeof value === 'string' && value.startsWith('-') ? '-2.5%' : '+1.5%'
  ),
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

  send(data: string) {
    // Mock send method
  }

  // Helper method to simulate receiving messages
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

describe('PoolDominance Component', () => {
  const mockPoolData: PoolData[] = [
    {
      rank: 1,
      pool: 'Test Pool 1',
      poolLink: 'https://testpool1.com',
      latestBlockHeight: 12345,
      hashrate: 1000000000000,
      blocks: 150,
      avgHealth: '95.5%',
      avgBlockFees: '+2.5%',
      emptyBlocks: 5,
    },
    {
      rank: 2,
      pool: 'Test Pool 2',
      poolLink: 'https://testpool2.com',
      latestBlockHeight: 12344,
      hashrate: 800000000000,
      blocks: 120,
      avgHealth: '92.1%',
      avgBlockFees: '-1.2%',
      emptyBlocks: 8,
    },
  ];

  let mockWs: MockWebSocket;

  beforeEach(() => {
    jest.clearAllMocks();
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
    test('renders the component with initial state', () => {
      render(<PoolDominance />);

      expect(screen.getByText('Pool Ranking')).toBeInTheDocument();
      expect(screen.getByText('1 Week')).toBeInTheDocument();
    });

    test('renders table headers on desktop view', () => {
      render(<PoolDominance />);

      const headers = [
        'Rank',
        'Pool',
        'Recent Block',
        'Hashrate',
        'Blocks',
        'Avg Health',
        'Avg Block Fees',
        'Empty Blocks',
      ];

      headers.forEach((header) => {
        expect(screen.getByText(header)).toBeInTheDocument();
      });
    });
  });

  describe('WebSocket Connection', () => {
    test('establishes WebSocket connection on mount', () => {
      render(<PoolDominance />);

      expect(global.WebSocket).toHaveBeenCalledWith(
        WEBSOCKET_URLS.MAIN_WEBSOCKET
      );
    });

    test('handles WebSocket connection opening', async () => {
      render(<PoolDominance />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });
    });

    test('handles WebSocket errors', async () => {
      const consoleSpy = jest.spyOn(console, 'error').mockImplementation();

      render(<PoolDominance />);

      await act(async () => {
        mockWs.simulateError();
      });

      expect(consoleSpy).toHaveBeenCalledWith(
        'WebSocket error:',
        expect.any(Event)
      );
      consoleSpy.mockRestore();
    });

    test('handles WebSocket close', async () => {
      const consoleSpy = jest.spyOn(console, 'log').mockImplementation();

      render(<PoolDominance />);

      await act(async () => {
        mockWs.close();
      });

      expect(consoleSpy).toHaveBeenCalledWith('WebSocket disconnected');
      consoleSpy.mockRestore();
    });
  });

  describe('Data Handling', () => {
    test('ignores non-pool_update messages', async () => {
      render(<PoolDominance />);
      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      await act(async () => {
        mockWs.simulateMessage({
          type: 'other_update',
          data: mockPoolData,
        });
      });

      // Pool data should not be rendered
      expect(screen.queryByText('Test Pool 1')).not.toBeInTheDocument();
    });

    test('handles malformed JSON messages', async () => {
      const consoleSpy = jest.spyOn(console, 'error').mockImplementation();

      render(<PoolDominance />);

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

      expect(consoleSpy).toHaveBeenCalledWith(
        'Error parsing websocket message :',
        expect.any(SyntaxError)
      );

      consoleSpy.mockRestore();
    });
  });

  describe('Data Rendering', () => {
    beforeEach(async () => {
      render(<PoolDominance />);

      await waitFor(() => {
        expect(mockWs.readyState).toBe(MockWebSocket.OPEN);
      });

      await act(async () => {
        mockWs.simulateMessage({
          type: 'pool_update',
          data: mockPoolData,
        });
      });
    });
    test('applies correct styling to positive and negative fees', () => {
      // The component should apply green color to positive fees and red to negative
      const positiveFeeElements = screen.getAllByText('+1.5%');
      const negativeFeeElements = screen.getAllByText('-2.5%');

      expect(positiveFeeElements[0]).toHaveClass('text-green-400');
      expect(negativeFeeElements[0]).toHaveClass('text-red-500');
    });

    test('renders external links with correct attributes', () => {
      const links = screen.getAllByRole('link');

      links.forEach((link) => {
        expect(link).toHaveAttribute('target', '_blank');
        expect(link).toHaveAttribute('rel', 'noopener noreferrer');
      });
    });
  });
});
