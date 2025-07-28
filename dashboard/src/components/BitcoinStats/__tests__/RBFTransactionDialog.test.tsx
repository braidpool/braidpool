import '@testing-library/jest-dom';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import RBFTransactionDialog from '../RBFTransactionDialog';
import { getTxInfo } from '../Utils';

// Create a separate copy mock so we can assert against it
const mockCopyToClipboard = jest.fn();

// Mock the utility functions including useCopyToClipboard hook
jest.mock('../Utils', () => ({
  getTxInfo: jest.fn(),
  useCopyToClipboard: () => [false, mockCopyToClipboard],
}));

// Mock CopyIcon
jest.mock('lucide-react', () => ({
  CopyIcon: () => <svg data-testid="copy-icon" />,
}));

// Mock navigator clipboard API
Object.assign(navigator, {
  clipboard: {
    writeText: jest.fn(),
  },
});

describe('RBFTransactionDialog', () => {
  const mockOnClose = jest.fn();
  const mockTxid = 'mock-txid-123';
  const mockTxInfo = {
    txid: 'mock-txid-123',
    status: { confirmed: false },
    fee: 1000,
    size: 250,
    weight: 600,
    version: 1,
    locktime: 0,
    vin: [
      {
        prevout: {
          scriptpubkey_address: 'address1',
          value: 500000000,
        },
      },
    ],
    vout: [
      {
        scriptpubkey_address: 'address2',
        value: 499000000,
      },
    ],
  };

  beforeEach(() => {
    jest.clearAllMocks();
    (getTxInfo as jest.Mock).mockReset();
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    (console.error as jest.Mock).mockRestore();
  });

  it('renders loading state initially', () => {
    (getTxInfo as jest.Mock).mockImplementation(() => new Promise(() => {}));
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    expect(screen.getByText('Loading transaction data...')).toBeInTheDocument();
  });

  it('fetches transaction data on mount', async () => {
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxInfo);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    await waitFor(() => {
      expect(getTxInfo).toHaveBeenCalledWith(mockTxid);
    });
  });

  it('displays transaction details when loaded', async () => {
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxInfo);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    await waitFor(() => {
      expect(screen.getByText(mockTxid)).toBeInTheDocument();
      expect(screen.getByText('Unconfirmed')).toBeInTheDocument();
      expect(screen.getByText('5 BTC')).toBeInTheDocument();
      expect(screen.getByText('4.99 BTC')).toBeInTheDocument();
      expect(screen.getByText('250 bytes')).toBeInTheDocument();
      expect(screen.getByText('600 WU')).toBeInTheDocument();
    });
  });

  it('displays error message when fetch fails', async () => {
    (getTxInfo as jest.Mock).mockRejectedValue(new Error('API error'));
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    await waitFor(() => {
      expect(
        screen.getByText('Failed to load transaction details')
      ).toBeInTheDocument();
    });
  });

  it('closes when overlay is clicked', async () => {
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxInfo);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    const overlay = screen.getByTestId('overlay');
    await userEvent.click(overlay);
    expect(mockOnClose).toHaveBeenCalled();
  });

  it('closes when close button is clicked', async () => {
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxInfo);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    const closeButton = await screen.findByLabelText('Close dialog');
    await userEvent.click(closeButton);
    expect(mockOnClose).toHaveBeenCalled();
  });

  it('copies transaction ID to clipboard using hook', async () => {
    (getTxInfo as jest.Mock).mockResolvedValue(mockTxInfo);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    const copyButton = await screen.findByLabelText('Copy transaction ID');
    await userEvent.click(copyButton);
    expect(mockCopyToClipboard).toHaveBeenCalledWith(mockTxid);
  });

  it('handles coinbase transactions', async () => {
    const coinbaseTx = {
      ...mockTxInfo,
      vin: [{ is_coinbase: true }],
    };
    (getTxInfo as jest.Mock).mockResolvedValue(coinbaseTx);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    await waitFor(() => {
      expect(screen.getByText('Coinbase')).toBeInTheDocument();
    });
  });

  it('updates when txid prop changes', async () => {
    const newTxid = 'new-txid-456';
    const newTxInfo = {
      ...mockTxInfo,
      txid: newTxid,
    };
    (getTxInfo as jest.Mock)
      .mockResolvedValueOnce(mockTxInfo)
      .mockResolvedValueOnce(newTxInfo);
    const { rerender } = render(
      <RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />
    );
    await screen.findByText(mockTxid);
    rerender(<RBFTransactionDialog txid={newTxid} onClose={mockOnClose} />);
    await waitFor(() => {
      expect(getTxInfo).toHaveBeenCalledWith(newTxid);
      expect(screen.getByText(newTxid)).toBeInTheDocument();
    });
  });

  it('displays correct number of inputs and outputs', async () => {
    const multiInputOutputTx = {
      ...mockTxInfo,
      vin: Array(3).fill(mockTxInfo.vin[0]),
      vout: Array(2).fill(mockTxInfo.vout[0]),
    };
    (getTxInfo as jest.Mock).mockResolvedValue(multiInputOutputTx);
    render(<RBFTransactionDialog txid={mockTxid} onClose={mockOnClose} />);
    await waitFor(() => {
      expect(screen.getByText('Inputs (3)')).toBeInTheDocument();
      expect(screen.getByText('Outputs (2)')).toBeInTheDocument();
      expect(screen.getAllByText(/From:/).length).toBe(3);
      expect(screen.getAllByText(/To:/).length).toBe(2);
    });
  });
});
