import { describe, it, expect, vi } from 'vitest';
import { render, screen } from '@testing-library/react';
import TransactionTable from '../TransactionTable';
import { TransactionCategory } from '@/types/transaction';

// Mock the Card component
vi.mock('@/components/common/Card', () => ({
    default: ({ title, subtitle, children }: any) => (
        <div data-testid="card">
            <h2>{title}</h2>
            <p>{subtitle}</p>
            {children}
        </div>
    ),
}));

// Mock colors
vi.mock('@/theme/colors', () => ({
    default: {
        primary: '#1976d2',
        secondary: '#ff9800',
    },
}));

const mockTransactions = [
    {
        txid: 'abc123',
        hash: 'abc123',
        category: TransactionCategory.MEMPOOL,
        size: 250,
        weight: 1000,
        fee: 0.00001,
        feeRate: 10.5,
        inputs: 2,
        outputs: 3,
        confirmations: 0,
        vin: [],
        vout: [],
        status: { confirmed: false },
        timestamp: Date.now() / 1000,
    },
];

describe('TransactionTable - Basic Tests', () => {
    it('renders without crashing', () => {
        render(<TransactionTable transactions={[]} />);
        expect(screen.getByRole('table')).toBeInTheDocument();
    });

    it('displays table headers', () => {
        render(<TransactionTable transactions={[]} />);

        expect(screen.getByText('Hash')).toBeInTheDocument();
        expect(screen.getByText('Category')).toBeInTheDocument();
        expect(screen.getByText('Fee (BTC)')).toBeInTheDocument();
    });

    it('shows loading spinner when loading', () => {
        render(<TransactionTable transactions={[]} loading={true} />);

        expect(screen.getByRole('progressbar')).toBeInTheDocument();
    });

    it('displays error message when provided', () => {
        render(<TransactionTable transactions={[]} error="Test error" />);

        expect(screen.getByText('Test error')).toBeInTheDocument();
    });

    it('shows empty state when no transactions', () => {
        render(<TransactionTable transactions={[]} />);

        expect(screen.getByText('No transactions found')).toBeInTheDocument();
    });

    it('renders transaction data when provided', () => {
        render(<TransactionTable transactions={mockTransactions} />);

        const table = screen.getByRole('table');
        expect(table).toBeInTheDocument();
    });
});