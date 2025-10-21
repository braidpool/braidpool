import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import TransactionsPage from '../TransactionsPage';
import { BraidPoolTransaction, TransactionCategory } from '@/types/transaction';

const mockTransactions: BraidPoolTransaction[] = [
  {
    txid: 'mock-tx-1',
    hash: 'mock-tx-1',
    category: TransactionCategory.MEMPOOL,
    size: 250,
    weight: 1000,
    fee: 0.00001,
    feeRate: 10.5,
    inputs: 2,
    outputs: 3,
    confirmations: 0,
    work: 100,
    workUnit: 'TH',
    vin: [],
    vout: [],
    status: { confirmed: false },
    timestamp: Date.now() / 1000,
    rbfSignaled: true,
  },
];

// Mock braidpoolApi
const mockFetchRecentTransactions = vi.fn();

vi.mock('@/utils/braidpoolApi', () => ({
  braidpoolApi: {
    fetchRecentTransactions: (...args: any[]) =>
      mockFetchRecentTransactions(...args),
  },
}));

// Mock TransactionTable component
vi.mock('../TransactionTable', () => ({
  default: ({
    transactions,
    loading,
    error,
    autoRefresh,
    refreshInterval,
    maxHeight,
  }: any) => (
    <div data-testid="transaction-table">
      <div data-testid="transactions-count">{transactions.length}</div>
      <div data-testid="loading-state">{loading ? 'loading' : 'loaded'}</div>
      <div data-testid="error-state">{error || 'no-error'}</div>
      <div data-testid="auto-refresh">
        {autoRefresh ? 'enabled' : 'disabled'}
      </div>
    </div>
  ),
}));

// Mock TopStatsBar component
vi.mock('@/components/common/TopStatsBar', () => ({
  default: () => <div data-testid="top-stats-bar">Stats Bar</div>,
}));

describe('TransactionsPage - Tailwind Tests', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockFetchRecentTransactions.mockResolvedValue(mockTransactions);
  });

  describe('Basic Rendering', () => {
    it('renders without crashing', () => {
      render(<TransactionsPage />);
      expect(screen.getByText('Transaction Management')).toBeInTheDocument();
    });

    it('displays page title', () => {
      render(<TransactionsPage />);
      expect(screen.getByText('Transaction Management')).toBeInTheDocument();
    });

    it('displays page description', () => {
      render(<TransactionsPage />);
      expect(
        screen.getByText(/Monitor and analyze Bitcoin transactions/)
      ).toBeInTheDocument();
    });

    it('renders TopStatsBar component', () => {
      render(<TransactionsPage />);
      expect(screen.getByTestId('top-stats-bar')).toBeInTheDocument();
    });

    it('renders TransactionTable component', async () => {
      render(<TransactionsPage />);
      await waitFor(() => {
        expect(screen.getByTestId('transaction-table')).toBeInTheDocument();
      });
    });
  });

  describe('Transaction Categories Section', () => {
    it('displays transaction categories section', () => {
      render(<TransactionsPage />);
      expect(screen.getByText('Transaction Categories')).toBeInTheDocument();
    });

    it('displays all category labels', () => {
      render(<TransactionsPage />);

      expect(screen.getByText('Mempool')).toBeInTheDocument();
      expect(screen.getByText('Committed')).toBeInTheDocument();
      expect(screen.getByText('Proposed')).toBeInTheDocument();
      expect(screen.getByText('Scheduled')).toBeInTheDocument();
      expect(screen.getByText('Confirmed')).toBeInTheDocument();
      expect(screen.getByText('Replaced')).toBeInTheDocument();
    });

    it('displays category descriptions', () => {
      render(<TransactionsPage />);

      expect(
        screen.getByText(/Transactions in bitcoind mempool only/)
      ).toBeInTheDocument();
      expect(
        screen.getByText(/Transactions committed to cmempool node/)
      ).toBeInTheDocument();
      expect(
        screen.getByText(/Transactions proposed for next block/)
      ).toBeInTheDocument();
    });
  });

  describe('Live Transaction Feed Section', () => {
    it('displays Live Transaction Feed title', () => {
      render(<TransactionsPage />);
      expect(screen.getByText('Live Transaction Feed')).toBeInTheDocument();
    });

    it('displays feed description', () => {
      render(<TransactionsPage />);
      expect(
        screen.getByText('Real-time Bitcoin transactions from your node')
      ).toBeInTheDocument();
    });

    it('displays Auto Refresh toggle', () => {
      render(<TransactionsPage />);
      expect(screen.getByText('Auto Refresh')).toBeInTheDocument();
    });
  });

  describe('Auto Refresh Toggle', () => {
    it('auto refresh checkbox is checked by default', async () => {
      render(<TransactionsPage />);

      const checkbox = screen.getByRole('checkbox');
      expect(checkbox).toBeChecked();

      await waitFor(() => {
        expect(screen.getByTestId('auto-refresh')).toBeInTheDocument();
      });
    });

    it('toggles auto refresh when clicked', async () => {
      render(<TransactionsPage />);

      const checkbox = screen.getByRole('checkbox');
      expect(checkbox).toBeChecked();

      // Click to disable
      fireEvent.click(checkbox);

      await waitFor(() => {
        expect(screen.getByTestId('auto-refresh')).toBeInTheDocument();
      });

      expect(checkbox).not.toBeChecked();
    });

    it('enables auto refresh when toggled back on', async () => {
      render(<TransactionsPage />);

      const checkbox = screen.getByRole('checkbox');

      // Disable
      fireEvent.click(checkbox);
      await waitFor(() => {
        expect(checkbox).not.toBeChecked();
      });

      // Re-enable
      fireEvent.click(checkbox);
      await waitFor(() => {
        expect(checkbox).toBeChecked();
      });
    });
  });

  describe('Data Fetching', () => {
    it('fetches transactions on mount', async () => {
      render(<TransactionsPage />);

      await waitFor(() => {
        expect(mockFetchRecentTransactions).toHaveBeenCalledWith(50);
      });
    });

    it('displays fetched transactions', async () => {
      render(<TransactionsPage />);

      await waitFor(() => {
        expect(screen.getByTestId('transactions-count')).toHaveTextContent('1');
      });
    });

    it('shows loading state initially', () => {
      render(<TransactionsPage />);
      expect(screen.getByTestId('loading-state')).toHaveTextContent('loading');
    });

    it('shows loaded state after fetch completes', async () => {
      render(<TransactionsPage />);

      await waitFor(() => {
        expect(screen.getByTestId('loading-state')).toHaveTextContent('loaded');
      });
    });
  });

  describe('Error Handling', () => {
    it('displays error message when fetch fails', async () => {
      mockFetchRecentTransactions.mockRejectedValueOnce(
        new Error('Network error')
      );

      render(<TransactionsPage />);

      await waitFor(() => {
        expect(screen.getByTestId('error-state')).toHaveTextContent(
          'Failed to load transactions. Please try again.'
        );
      });
    });

    it('logs error to console when fetch fails', async () => {
      const consoleSpy = vi
        .spyOn(console, 'error')
        .mockImplementation(() => {});
      mockFetchRecentTransactions.mockRejectedValueOnce(new Error('API Error'));

      render(<TransactionsPage />);

      await waitFor(() => {
        expect(consoleSpy).toHaveBeenCalledWith(
          'Failed to fetch transactions:',
          expect.any(Error)
        );
      });

      consoleSpy.mockRestore();
    });
  });

  describe('Props Passed to TransactionTable', () => {
    it('passes correct props to TransactionTable', async () => {
      render(<TransactionsPage />);

      await waitFor(() => {
        expect(screen.getByTestId('transaction-table')).toBeInTheDocument();
      });

      expect(screen.getByTestId('auto-refresh')).toHaveTextContent('enabled');
    });

    it('passes transactions data to TransactionTable', async () => {
      render(<TransactionsPage />);

      await waitFor(() => {
        expect(screen.getByTestId('transactions-count')).toBeInTheDocument();
      });

      expect(screen.getByTestId('transactions-count')).toHaveTextContent('1');
    });
  });

  describe('Tailwind Styling', () => {
    it('renders toggle switch', () => {
      render(<TransactionsPage />);
      const checkbox = screen.getByRole('checkbox');
      expect(checkbox).toBeInTheDocument();
    });

    it('displays all required UI elements', () => {
      render(<TransactionsPage />);
      expect(screen.getByText('Transaction Management')).toBeInTheDocument();
      expect(screen.getByText('Transaction Categories')).toBeInTheDocument();
      expect(screen.getByText('Live Transaction Feed')).toBeInTheDocument();
    });
  });
});
