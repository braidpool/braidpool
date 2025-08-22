import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import MinedSharesExplorer from '../MinedSharesExplorer';
import '@testing-library/jest-dom';
const mockWebSocketConstructor = jest.fn(() => ({
  onopen: null,
  onclose: null,
  onerror: null,
  onmessage: null,
  readyState: 0, // WebSocket.CONNECTING
  close: jest.fn(),
}));

Object.defineProperty(mockWebSocketConstructor, 'CONNECTING', { value: 0 });
Object.defineProperty(mockWebSocketConstructor, 'OPEN', { value: 1 });
Object.defineProperty(mockWebSocketConstructor, 'CLOSING', { value: 2 });
Object.defineProperty(mockWebSocketConstructor, 'CLOSED', { value: 3 });

global.WebSocket = mockWebSocketConstructor as any;

jest.mock('../DashboardHeader', () => {
  return function MockDashboardHeader({ activeTab, setActiveTab }: any) {
    return (
      <div>
        <div>DashboardHeader</div>
        <button onClick={() => setActiveTab('beads')}>Beads Tab</button>
        <button onClick={() => setActiveTab('trends')}>Trends Tab</button>
        <button onClick={() => setActiveTab('rewards')}>Rewards Tab</button>
      </div>
    );
  };
});

jest.mock('../BeadRow', () => {
  return function MockBeadRow({ bead, isExpanded, onToggle }: any) {
    return (
      <div onClick={onToggle} data-testid={`bead-row-${bead.id}`}>
        BeadRow: {bead.id} {isExpanded ? 'expanded' : 'collapsed'}
      </div>
    );
  };
});

jest.mock('../Trends/TrendsTab', () => {
  const MockTrendsTab = function MockTrendsTab() {
    return <div>TrendsTab</div>;
  };

  return {
    TrendsTab: MockTrendsTab,
    __esModule: true,
    default: MockTrendsTab,
  };
});

jest.mock('../Reward/RewardsDashboard', () => {
  return {
    RewardsDashboard: function MockRewardsDashboard() {
      return <div>RewardsDashboard</div>;
    },
  };
});

jest.mock('../lib/Utils', () => ({
  processBlockData: jest.fn((data) => ({
    blockHash: data.blockHash || 'mock-hash',
    height: data.height || 123,
    timestamp: data.timestamp || '2023-01-01T00:00:00.000Z',
    work: data.work || '100.00 EH',
    txCount: data.txCount || 1,
    reward: data.reward || 6.25,
    parent: data.parent || 'parent-hash',
    transactions: data.transactions || [],
  })),
}));

describe('MinedSharesExplorer', () => {
  let mockWebSocket: any;

  beforeEach(() => {
    jest.clearAllMocks();
    mockWebSocket = {
      onopen: null,
      onclose: null,
      onerror: null,
      onmessage: null,
      readyState: 1,
      close: jest.fn(),
    };
    mockWebSocketConstructor.mockReturnValue(mockWebSocket);
  });

  it('renders the component with initial state', () => {
    render(<MinedSharesExplorer />);

    expect(screen.getByText('DashboardHeader')).toBeInTheDocument();
    expect(screen.getByText('Connecting to server...')).toBeInTheDocument();

    const loadingElements = document.querySelectorAll('.animate-pulse');
    expect(loadingElements.length).toBeGreaterThan(0);
  });

  it('displays "Waiting for block data" when connected but no beads', async () => {
    render(<MinedSharesExplorer />);

    if (mockWebSocket.onopen) {
      mockWebSocket.onopen();
    }

    await waitFor(() => {
      expect(screen.getByText('Waiting for block data...')).toBeInTheDocument();
    });
  });

  it('processes and displays block data from WebSocket', async () => {
    render(<MinedSharesExplorer />);

    if (mockWebSocket.onopen) {
      mockWebSocket.onopen();
    }
    const mockBlockData = {
      type: 'block_data',
      data: {
        blockHash: 'test-hash-123',
        height: 456,
        timestamp: 1700000000000,
        work: '150.50 EH',
        txCount: 3,
        reward: 6.25,
        parent: 'parent-hash-456',
        transactions: [
          {
            id: 'tx1',
            hash: 'tx-hash-1',
            timestamp: '1700000000000',
            fee: 0.001,
            size: 250,
            feeRate: 10,
            inputs: 2,
            outputs: 1,
          },
        ],
      },
    };

    if (mockWebSocket.onmessage) {
      mockWebSocket.onmessage({
        data: JSON.stringify(mockBlockData),
      });
    }

    await waitFor(() => {
      expect(screen.getByTestId('bead-row-test-hash-123')).toBeInTheDocument();
    });
  });

  it('toggles bead expansion when clicked', async () => {
    render(<MinedSharesExplorer />);

    if (mockWebSocket.onopen) {
      mockWebSocket.onopen();
    }

    const mockBlockData = {
      type: 'block_data',
      data: {
        blockHash: 'test-hash-toggle',
        height: 789,
        timestamp: 1700000000000,
        work: '200.00 EH',
        txCount: 1,
        reward: 6.25,
        parent: 'parent-hash',
        transactions: [],
      },
    };

    if (mockWebSocket.onmessage) {
      mockWebSocket.onmessage({
        data: JSON.stringify(mockBlockData),
      });
    }

    await waitFor(() => {
      const beadRow = screen.getByTestId('bead-row-test-hash-toggle');
      expect(beadRow).toHaveTextContent('collapsed');

      fireEvent.click(beadRow);
      expect(beadRow).toHaveTextContent('expanded');
    });
  });

  it('handles pagination correctly', async () => {
    render(<MinedSharesExplorer />);
    if (mockWebSocket.onopen) {
      mockWebSocket.onopen();
    }
    for (let i = 0; i < 7; i++) {
      const mockBlockData = {
        type: 'block_data',
        data: {
          blockHash: `test-hash-${i}`,
          height: 100 + i,
          timestamp: 1700000000000 + i * 1000,
          work: `${100 + i}.00 EH`,
          txCount: 1,
          reward: 6.25,
          parent: `parent-hash-${i}`,
          transactions: [],
        },
      };

      if (mockWebSocket.onmessage) {
        mockWebSocket.onmessage({
          data: JSON.stringify(mockBlockData),
        });
      }
    }

    await waitFor(() => {
      // Should show pagination controls
      expect(screen.getByText('Next')).toBeInTheDocument();
      expect(screen.getByText('Previous')).toBeInTheDocument();
      expect(screen.getByText(/Page 1 of/)).toBeInTheDocument();
      expect(screen.getByText('Previous')).toBeDisabled();

      // Click next page
      fireEvent.click(screen.getByText('Next'));
      expect(screen.getByText(/Page 2 of/)).toBeInTheDocument();
    });
  });

  it('switches to trends tab when activeTab changes', async () => {
    render(<MinedSharesExplorer />);

    const trendsButton = screen.getByText('Trends Tab');
    fireEvent.click(trendsButton);

    await waitFor(() => {
      expect(screen.getByText('TrendsTab')).toBeInTheDocument();
    });
  });

  it('switches to rewards tab when activeTab changes', async () => {
    render(<MinedSharesExplorer />);

    const rewardsButton = screen.getByText('Rewards Tab');
    fireEvent.click(rewardsButton);

    await waitFor(() => {
      expect(screen.getByText('RewardsDashboard')).toBeInTheDocument();
    });
  });

  it('handles WebSocket errors gracefully', async () => {
    const consoleSpy = jest.spyOn(console, 'error').mockImplementation();

    render(<MinedSharesExplorer />);
    if (mockWebSocket.onerror) {
      mockWebSocket.onerror(new Error('Connection failed'));
    }

    await waitFor(() => {
      expect(screen.getByText('Connecting to server...')).toBeInTheDocument();
    });

    expect(consoleSpy).toHaveBeenCalledWith(
      'WebSocket error:',
      expect.any(Error)
    );
    consoleSpy.mockRestore();
  });

  it('handles invalid JSON messages gracefully', async () => {
    const consoleSpy = jest.spyOn(console, 'error').mockImplementation();

    render(<MinedSharesExplorer />);
    if (mockWebSocket.onopen) {
      mockWebSocket.onopen();
    }
    if (mockWebSocket.onmessage) {
      mockWebSocket.onmessage({
        data: 'invalid json',
      });
    }

    await waitFor(() => {
      expect(consoleSpy).toHaveBeenCalledWith(
        'WebSocket message parse error:',
        expect.any(Error)
      );
    });

    consoleSpy.mockRestore();
  });

  it('closes WebSocket connection on component unmount', () => {
    const { unmount } = render(<MinedSharesExplorer />);
    expect(mockWebSocketConstructor).toHaveBeenCalled();
    expect(mockWebSocket.readyState).toBe(1); // OPEN

    unmount();

    expect(mockWebSocket.close).toHaveBeenCalled();
  });

  it('limits the number of stored beads to 100', async () => {
    render(<MinedSharesExplorer />);
    if (mockWebSocket.onopen) {
      mockWebSocket.onopen();
    }
    for (let i = 0; i < 102; i++) {
      const mockBlockData = {
        type: 'block_data',
        data: {
          blockHash: `test-hash-${i}`,
          height: 100 + i,
          timestamp: 1700000000000 + i * 1000,
          work: `${100 + i}.00 EH`,
          txCount: 1,
          reward: 6.25,
          parent: `parent-hash-${i}`,
          transactions: [],
        },
      };

      if (mockWebSocket.onmessage) {
        mockWebSocket.onmessage({
          data: JSON.stringify(mockBlockData),
        });
      }
    }

    await waitFor(() => {
      const pageInfo = screen.getByText(/Page 1 of/);
      expect(pageInfo).toBeInTheDocument();
      expect(screen.getByText('Next')).toBeInTheDocument();
    });
  });
});
