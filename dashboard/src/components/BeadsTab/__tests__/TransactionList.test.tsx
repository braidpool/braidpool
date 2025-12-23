import { render, screen, fireEvent } from '@testing-library/react';
import TransactionList from '../TransactionList';
import { Transaction } from '../lib/Types';

// Mock shortenHash and useCopyToClipboard
const mockCopy = jest.fn();
jest.mock('../lib/Utils', () => ({
  shortenHash: jest.fn((hash) => `short:${hash}`),
  useCopyToClipboard: () => ({
    copied: 'mock-hash-1',
    copy: mockCopy,
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
  beforeEach(() => {
    mockCopy.mockClear();
  });

  it('renders header and limited transactions', () => {
    render(<TransactionList transactions={mockTransactions} />);
    expect(
      screen.getByText(/Showing 10 of 12 Transactions/i)
    ).toBeInTheDocument();
    expect(screen.getByText(/\(displaying first 10\)/i)).toBeInTheDocument();
    expect(screen.getByText('Hash')).toBeInTheDocument();
    expect(screen.getAllByText(/short:mock-hash/)).toHaveLength(20);
  });

  it('renders transaction fields correctly', () => {
    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    const tx = mockTransactions[0];
    // Each hash appears twice (desktop + mobile)
    expect(screen.getAllByText(`short:${tx.hash}`)).toHaveLength(2);
    expect(screen.getAllByText(`${tx.size} vB`)).toHaveLength(1); // desktop only
    expect(screen.getAllByText(`${tx.size}vB`)).toHaveLength(1); // mobile only
    expect(screen.getAllByText(`${tx.fee.toFixed(8)} BTC`)).toHaveLength(2);
    expect(
      screen.getAllByText(`${tx.feeRate.toFixed(2)} sats/vB`)
    ).toHaveLength(2);
    expect(screen.getAllByText(`${tx.inputs}`)).toHaveLength(2);
    expect(screen.getAllByText(`${tx.outputs}`)).toHaveLength(2);
  });

  it('shows "Copied!" label for copied transaction hash', () => {
    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    expect(screen.getAllByText(/Copied!/i)).toHaveLength(2);
  });

  it('calls copy function on hash button click', () => {
    jest.mocked(require('../lib/Utils')).useCopyToClipboard = () => ({
      copied: '',
      copy: mockCopy,
    });

    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    const buttons = screen.getAllByText(/short:mock-hash-1/);
    fireEvent.click(buttons[0]);
    expect(mockCopy).toHaveBeenCalledWith('mock-hash-1');
  });
});
