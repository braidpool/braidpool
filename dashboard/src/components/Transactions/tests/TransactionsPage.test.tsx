import { describe, it, expect, vi } from 'vitest';
import { render, screen } from '@testing-library/react';
import TransactionsPage from '../TransactionsPage';

// Mock dependencies
vi.mock('@/utils/braidpoolApi', () => ({
    braidpoolApi: {
        fetchRecentTransactions: vi.fn().mockResolvedValue([]),
    },
}));

vi.mock('../TransactionTable', () => ({
    default: () => <div data-testid="transaction-table">Mocked Table</div>,
}));

vi.mock('@/components/common/TopStatsBar', () => ({
    default: () => <div data-testid="top-stats-bar">Stats</div>,
}));

vi.mock('@/theme/colors', () => ({
    default: {
        background: '#000',
        textPrimary: '#fff',
        textSecondary: '#aaa',
        primary: '#1976d2',
    },
}));

describe('TransactionsPage - Basic Tests', () => {
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

        expect(screen.getByText(/Monitor and analyze Bitcoin transactions/)).toBeInTheDocument();
    });

    it('renders TopStatsBar component', () => {
        render(<TransactionsPage />);

        expect(screen.getByTestId('top-stats-bar')).toBeInTheDocument();
    });

    it('renders TransactionTable component', () => {
        render(<TransactionsPage />);

        expect(screen.getByTestId('transaction-table')).toBeInTheDocument();
    });

    it('displays transaction categories section', () => {
        render(<TransactionsPage />);

        expect(screen.getByText('Transaction Categories')).toBeInTheDocument();
    });

    it('displays all category labels', () => {
        render(<TransactionsPage />);

        expect(screen.getByText('Mempool')).toBeInTheDocument();
        expect(screen.getByText('Committed')).toBeInTheDocument();
        expect(screen.getByText('Confirmed')).toBeInTheDocument();
    });
});