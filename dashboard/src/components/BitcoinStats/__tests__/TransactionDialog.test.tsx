import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import TransactionDialog from '../TransactionDialog';
import * as utils from '../Utils';
import '@testing-library/jest-dom';

// Mocking getTxInfo
jest.mock('../Utils', () => ({
  getTxInfo: jest.fn(),
}));

const mockTxData = {
  txid: 'sample-txid-123',
  status: { confirmed: true },
  fee: 10000,
  size: 250,
  weight: 1000,
  version: 2,
  locktime: 0,
  vin: [
    {
      prevout: {
        scriptpubkey_address: 'address1',
        value: 5000000000,
      },
    },
  ],
  vout: [
    {
      scriptpubkey_address: 'address2',
      value: 4999990000,
    },
  ],
};

describe('TransactionDialog', () => {
  it('renders transaction info after loading', async () => {
    (utils.getTxInfo as jest.Mock).mockResolvedValue(mockTxData);

    const onClose = jest.fn();

    render(<TransactionDialog txid="sample-txid-123" onClose={onClose} />);

    // Initially shows loading
    expect(screen.getByText(/Loading transaction data/i)).toBeInTheDocument();

    // Wait for transaction data to appear
    await waitFor(() =>
      expect(screen.getByText(/Transaction ID/i)).toBeInTheDocument()
    );

    expect(screen.getByText(/sample-txid-123/i)).toBeInTheDocument();
    expect(screen.getByText(/Confirmed/i)).toBeInTheDocument();
    expect(screen.getByText(/0.0001 BTC/i)).toBeInTheDocument(); // fee
    expect(screen.getByText(/address1/i)).toBeInTheDocument(); // input address
    expect(screen.getByText(/address2/i)).toBeInTheDocument(); // output address

    // Simulate close
    fireEvent.click(screen.getByText('✕'));
    expect(onClose).toHaveBeenCalled();
  });
});
