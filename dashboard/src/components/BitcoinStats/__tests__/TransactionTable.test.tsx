import { render, screen, waitFor } from '@testing-library/react';
import TransactionDialog from '../TransactionDialog';
import * as Utils from '../Utils';
import '@testing-library/jest-dom';

jest.mock('../Utils');

// Mock clipboard
Object.assign(navigator, {
  clipboard: {
    writeText: jest.fn(),
  },
});

const mockOnClose = jest.fn();

describe('TransactionDialog', () => {
  it('renders inputs and outputs when present', async () => {
    const mockTxInfo = {
      txid: 'abc123',
      status: { confirmed: true },
      fee: 1000,
      size: 250,
      weight: 1000,
      version: 2,
      locktime: 0,
      vin: [
        {
          prevout: {
            scriptpubkey_address: 'inputAddress',
            value: 5000000000,
          },
        },
      ],
      vout: [
        {
          scriptpubkey_address: 'outputAddress',
          value: 2500000000,
        },
      ],
    };

    (Utils.getTxInfo as jest.Mock).mockResolvedValue(mockTxInfo);

    render(<TransactionDialog txid="abc123" onClose={mockOnClose} />);

    await waitFor(() => {
      expect(screen.getByText(/Inputs \(1\)/)).toBeInTheDocument();
      expect(screen.getByText(/Outputs \(1\)/)).toBeInTheDocument();
      expect(screen.getByText('inputAddress')).toBeInTheDocument();
      expect(screen.getByText('outputAddress')).toBeInTheDocument();
    });
  });
});
