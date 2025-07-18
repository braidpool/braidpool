import React from 'react';
import { render, screen, fireEvent } from '@testing-library/react';
import RBFTransactionTable from '../RBFTransactionTable';
import '@testing-library/jest-dom';

// Mock RBFTransactionDialog
jest.mock('../RBFTransactionDialog', () => ({
  __esModule: true,
  default: ({ txid, onClose }: { txid: string; onClose: () => void }) => (
    <div data-testid="rbf-dialog">
      Dialog for {txid}
      <button onClick={onClose}>Close</button>
    </div>
  ),
}));

// Mock RBFTransactionRow
jest.mock('../RBFTransactionRow', () => ({
  __esModule: true,
  RBFTransactionRow: ({
    tx,
    onSelect,
  }: {
    tx: any;
    onSelect: (txid: string) => void;
  }) => (
    <tr data-testid="rbf-row">
      <td>
        <button onClick={() => onSelect(tx.tx.txid)}>{tx.tx.txid}</button>
      </td>
      <td>{tx.tx.fee}</td>
      <td>{tx.tx.value}</td>
      <td>{tx.rate}</td>
      <td>{String(tx.rbf)}</td>
    </tr>
  ),
}));

describe('RBFTransactionTable', () => {
  it('renders fallback message when transaction list is empty', () => {
    render(<RBFTransactionTable transactions={[]} />);
    expect(screen.getByText(/no rbf transactions found/i)).toBeInTheDocument();
    expect(screen.queryByRole('columnheader')).not.toBeInTheDocument();
  });

  it('renders a transaction row when transactions exist', () => {
    const mockTx = {
      tx: { txid: 'rbf123', fee: 900, value: 50000 },
      rate: 15,
      rbf: true,
    };

    render(<RBFTransactionTable transactions={[mockTx]} />);

    expect(screen.getByText('rbf123')).toBeInTheDocument();
    expect(screen.getByText('900')).toBeInTheDocument();
    expect(screen.getByText('50000')).toBeInTheDocument();
    expect(screen.getByText('15')).toBeInTheDocument();
    expect(screen.getByText('true')).toBeInTheDocument();
  });

  it('opens dialog on transaction click and closes it on "Close"', () => {
    const mockTx = {
      tx: { txid: 'rbf456', fee: 700, value: 60000 },
      rate: 10,
      rbf: false,
    };

    render(<RBFTransactionTable transactions={[mockTx]} />);
    fireEvent.click(screen.getByText('rbf456'));

    expect(screen.getByTestId('rbf-dialog')).toBeInTheDocument();
    expect(screen.getByText(/dialog for rbf456/i)).toBeInTheDocument();

    fireEvent.click(screen.getByText('Close'));
    expect(screen.queryByTestId('rbf-dialog')).not.toBeInTheDocument();
  });
});
