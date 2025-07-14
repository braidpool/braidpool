import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import TransactionDialog from '../TransactionDialog';
import { getTxInfo } from '../Utils';
import '@testing-library/jest-dom';
import userEvent from '@testing-library/user-event';

const mockCopyToClipboard = jest.fn();

jest.mock('../Utils', () => ({
  ...jest.requireActual('../Utils'),
  getTxInfo: jest.fn(),
  useCopyToClipboard: () => [false, mockCopyToClipboard],
}));

jest.mock('lucide-react', () => ({
  CopyIcon: () => <svg data-testid="copy-icon" />,
}));

Object.assign(navigator, {
  clipboard: {
    writeText: jest.fn(),
  },
});

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
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxData);

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

  it('copies transaction ID to clipboard using hook', async () => {
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxData);

    render(<TransactionDialog txid={mockTxData.txid} onClose={jest.fn()} />);
    const copyButton = await screen.findByLabelText('Copy transaction ID');
    await userEvent.click(copyButton);

    expect(mockCopyToClipboard).toHaveBeenCalledWith(mockTxData.txid);
  });
});
