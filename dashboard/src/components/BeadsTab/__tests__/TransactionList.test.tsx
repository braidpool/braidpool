import { render, screen, fireEvent } from '@testing-library/react';
import TransactionList from '../TransactionList';
import { Transaction } from '../lib/Types';

// Mock shortenHash and useCopyToClipboard
jest.mock('../lib/Utils', () => ({
  shortenHash: jest.fn((hash) => `short:${hash}`),
  useCopyToClipboard: () => ({
    copied: 'mock-hash-1',
    copy: jest.fn(),
  }),
}));

const mockTransactions: Transaction[] = Array.from({ length: 12 }, (_, i) => ({
  id: `tx-${i + 1}`,
  hash: `mock-hash-${i + 1}`,
  timestamp: new Date().toISOString(),
  count: 1,
  blockId: `block-${i + 1}`,
  fee: 0.00001234,
  size: 250,
  feePaid: '0.00001234',
  feeRate: 1.23,
  inputs: 1,
  outputs: 2,
}));

describe('<TransactionList />', () => {
  it('renders header and limited transactions', () => {
    render(<TransactionList transactions={mockTransactions} />);

    expect(
      screen.getByText(/Showing 10 of 12 Transactions/i)
    ).toBeInTheDocument();
    expect(screen.getByText(/\(displaying first 10\)/i)).toBeInTheDocument();
    expect(screen.getByText('Hash')).toBeInTheDocument();
    expect(screen.getAllByText(/short:mock-hash/)).toHaveLength(10); // only first 10
  });

  it('renders transaction fields correctly', () => {
    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    const tx = mockTransactions[0];

    expect(screen.getByText(`short:${tx.hash}`)).toBeInTheDocument();
    expect(screen.getByText(`${tx.size} vB`)).toBeInTheDocument();
    expect(screen.getByText(`${tx.fee.toFixed(8)} BTC`)).toBeInTheDocument();
    expect(
      screen.getByText(`${tx.feeRate.toFixed(2)} sats/vB`)
    ).toBeInTheDocument();
    expect(screen.getByText(`${tx.inputs}`)).toBeInTheDocument();
    expect(screen.getByText(`${tx.outputs}`)).toBeInTheDocument();
  });

  it('shows "Copied!" label for copied transaction hash', () => {
    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    expect(screen.getByText(/Copied!/i)).toBeInTheDocument();
  });

  it('calls copy function on hash button click', () => {
    const mockCopy = jest.fn();
    jest.mocked(require('../lib/Utils')).useCopyToClipboard = () => ({
      copied: '',
      copy: mockCopy,
    });

    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    const button = screen.getByText(/short:mock-hash-1/);
    fireEvent.click(button);
    expect(mockCopy).toHaveBeenCalledWith('mock-hash-1');
  });
});
