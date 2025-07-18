import '@testing-library/jest-dom';
import { render, screen, fireEvent } from '@testing-library/react';
import TransactionTable from '../TransactionTable';

jest.mock('../TransactionDialog', () => ({
  __esModule: true,
  default: ({ txid, onClose }: { txid: string; onClose: () => void }) => (
    <div data-testid="transaction-dialog">
      Dialog for {txid}
      <button onClick={onClose}>Close</button>
    </div>
  ),
}));

describe('TransactionTable', () => {
  it('renders "No transactions found" message when empty', () => {
    render(<TransactionTable transactions={[]} />);
    expect(screen.getByText(/no transactions found/i)).toBeInTheDocument();
    expect(screen.queryByText(/TXID/i)).not.toBeInTheDocument(); // No headers
  });

  it('renders transactions and table headers when data is present', () => {
    const mockTx = [
      {
        txid: 'abcdefgh12345678',
        fee: 1000,
        vsize: 225,
        value: 2500000000,
      },
    ];

    render(<TransactionTable transactions={mockTx} />);

    // Headers
    expect(screen.getByText(/TXID/i)).toBeInTheDocument();
    expect(screen.getByText(/FEE/i)).toBeInTheDocument();
    expect(screen.getByText(/SIZE/i)).toBeInTheDocument();
    expect(screen.getByText(/VALUE/i)).toBeInTheDocument();

    // Row Data
    expect(screen.getByText(/abcdefg....2345678/)).toBeInTheDocument(); // shortened txid
    expect(screen.getByText(/0.00001 BTC/i)).toBeInTheDocument(); // fee
    expect(screen.getByText(/225 vB/)).toBeInTheDocument(); // size
    expect(screen.getByText(/25 BTC/)).toBeInTheDocument(); // value
  });
});
