import '@testing-library/jest-dom';
import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import BlockInfoDialog from '../BlockDialog';
import { getBlockInfo } from '../Utils';
import userEvent from '@testing-library/user-event';

const mockCopyToClipboard = jest.fn();

jest.mock('../Utils', () => ({
  ...jest.requireActual('../Utils'),
  getBlockInfo: jest.fn(),
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

const mockBlockInfo = {
  id: '0000000000000000000bba9f...',
  height: 123456,
  timestamp: 1717653123,
  version: 1,
  bits: '1a2b3c',
  nonce: 234567,
  difficulty: 1234567890,
  merkle_root: 'abcd1234efgh5678',
  tx_count: 2000,
  size: 123456,
  weight: 400000,
  previousblockhash: '0000000000000000000aabb...',
  extras: {
    reward: 625000000,
    totalFees: 5000000,
    pool: { name: 'F2Pool' },
    matchRate: 95.7,
    medianFee: 15,
  },
};

describe('BlockInfoDialog', () => {
  const onClose = jest.fn();

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('shows loading indicator initially', async () => {
    (getBlockInfo as jest.Mock).mockReturnValue(new Promise(() => {}));

    render(<BlockInfoDialog hash="testhash" onClose={onClose} />);
    expect(screen.getByText(/loading block data/i)).toBeInTheDocument();
  });

  it('displays error message on fetch failure', async () => {
    (getBlockInfo as jest.Mock).mockRejectedValue(new Error('Fetch error'));

    render(<BlockInfoDialog hash="badHash" onClose={onClose} />);
    await waitFor(() =>
      expect(
        screen.getByText(/failed to load block details/i)
      ).toBeInTheDocument()
    );
  });

  it('renders block details on success', async () => {
    (getBlockInfo as jest.Mock).mockResolvedValue(mockBlockInfo);

    render(<BlockInfoDialog hash="goodHash" onClose={onClose} />);
    await waitFor(() =>
      expect(screen.getByText(/Block ID \(Hash\)/)).toBeInTheDocument()
    );

    expect(screen.getByText(mockBlockInfo.id)).toBeInTheDocument();
    expect(
      screen.getByText(mockBlockInfo.height.toString())
    ).toBeInTheDocument();
    expect(screen.getByText(/F2Pool/)).toBeInTheDocument();
  });

  it('copies block ID to clipboard using hook', async () => {
    (getBlockInfo as jest.Mock).mockResolvedValue(mockBlockInfo);

    render(<BlockInfoDialog hash={mockBlockInfo.id} onClose={jest.fn()} />);
    const copyButton = await screen.findByLabelText('Copy block hash');
    await userEvent.click(copyButton);
    expect(mockCopyToClipboard).toHaveBeenCalledWith(mockBlockInfo.id);
  });

  it('calls onClose when background is clicked', async () => {
    (getBlockInfo as jest.Mock).mockResolvedValue(mockBlockInfo);

    render(<BlockInfoDialog hash="hashToClose" onClose={onClose} />);
    await screen.findByText(mockBlockInfo.id);

    const overlay = screen.getByTestId('overlay');
    fireEvent.click(overlay);
    expect(onClose).toHaveBeenCalled();
  });
});
