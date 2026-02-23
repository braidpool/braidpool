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
    // Headers - match actual TransactionTable.tsx headers
    // Headers - use role-based selectors to avoid button text conflicts
    const headers = screen.getAllByRole('columnheader');
    const headerTexts = headers.map(h => h.textContent);
    
    expect(headerTexts).toContain('TXID');
    expect(headerTexts).toContain('CATEGORY');
    expect(headerTexts).toContain('FEE');
    expect(headerTexts).toContain('FEE RATE');
    expect(headerTexts).toContain('SIZE');
    expect(headerTexts).toContain('I/O');
    expect(headerTexts).toContain('STATUS');
    expect(headerTexts).toContain('TIME');

    // Row Data
    expect(screen.getByText(/abcdefg....2345678/)).toBeInTheDocument(); // shortened txid
    expect(screen.getByText(/1000.00000000/)).toBeInTheDocument();  // fee
    expect(screen.getByText(/BTC/)).toBeInTheDocument(); // fee unit
  });
});
