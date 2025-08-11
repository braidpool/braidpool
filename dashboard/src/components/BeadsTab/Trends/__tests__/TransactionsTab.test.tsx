import { render, screen, fireEvent } from '@testing-library/react';
import TransactionList from '../../TransactionList';
import { Transaction } from '../../lib/Types';

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

    // Use getAllByText to account for both desktop and mobile views (10 desktop + 10 mobile = 20)
    expect(screen.getAllByText(/short:mock-hash/)).toHaveLength(20);
  });

  it('renders transaction fields correctly', () => {
    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    const tx = mockTransactions[0];

    // Use getAllByText for elements that appear in both desktop and mobile views
    expect(screen.getAllByText(`short:${tx.hash}`)).toHaveLength(2); // desktop + mobile
    expect(screen.getByText(`${tx.size} vB`)).toBeInTheDocument(); // desktop version
    expect(screen.getByText(`${tx.fee.toFixed(8)} BTC`)).toBeInTheDocument(); // desktop version
    expect(
      screen.getByText(`${tx.feeRate.toFixed(2)} sats/vB`)
    ).toBeInTheDocument(); // desktop version
    expect(screen.getAllByText(`${tx.inputs}`)).toHaveLength(2); // desktop + mobile
    expect(screen.getAllByText(`${tx.outputs}`)).toHaveLength(2); // desktop + mobile
  });

  it('shows "Copied!" label for copied transaction hash', () => {
    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);
    // Use getAllByText since "Copied!" appears in both desktop and mobile views
    expect(screen.getAllByText(/Copied!/i)).toHaveLength(2);
  });

  it('calls copy function on hash button click', () => {
    // Mock useCopyToClipboard to return empty copied state for this test
    jest.mocked(require('../lib/Utils')).useCopyToClipboard = () => ({
      copied: '',
      copy: mockCopy,
    });

    render(<TransactionList transactions={mockTransactions.slice(0, 1)} />);

    // Get all buttons with the hash text (there will be 2: desktop + mobile)
    const buttons = screen.getAllByText(/short:mock-hash-1/);

    // Click the first button (desktop view)
    fireEvent.click(buttons[0]);
    expect(mockCopy).toHaveBeenCalledWith('mock-hash-1');
  });
});
