import '@testing-library/jest-dom';
import { render, screen, fireEvent } from '@testing-library/react';
import RecentBlocksTable from '../RecentBlocksTable';
import { Block } from '../Types';

// Mock the BlockDialog
jest.mock('../BlockDialog', () => ({ hash, onClose }: any) => (
  <div data-testid="block-dialog">
    Block Dialog: {hash}
    <button onClick={onClose}>Close</button>
  </div>
));

// Mock utilities
jest.mock('../../../theme/colors', () => ({
  primary: '#ff0000',
  paper: '#121212',
  textPrimary: '#ffffff',
  textSecondary: '#cccccc',
  accent: '#00ffff',
  cardAccentSecondary: '#333333',
}));

jest.mock('../../BitcoinStats/Utils', () => ({
  shortenAddress: (addr: string) => `short:${addr.slice(0, 4)}`,
}));

jest.mock('../Utils', () => ({
  formatUnixTimestamp: (ts: number) => `formatted:${ts}`,
}));

const createMockBlock = (
  id: string,
  height: number,
  timestamp: number
): Block => ({
  id,
  height,
  version: 1,
  timestamp,
  bits: 0,
  nonce: 0,
  difficulty: 0,
  merkle_root: '',
  tx_count: 1,
  size: 100,
  weight: 200,
  previousblockhash: '',
  mediantime: timestamp,
  stale: false,
  extras: {
    reward: 0,
    coinbaseRaw: '',
    orphans: [],
    medianFee: 0,
    feeRange: [],
    totalFees: 0,
    avgFee: 0,
    avgFeeRate: 0,
    utxoSetChange: 0,
    avgTxSize: 0,
    totalInputs: 0,
    totalOutputs: 0,
    totalOutputAmt: 0,
    segwitTotalTxs: 0,
    segwitTotalSize: 0,
    segwitTotalWeight: 0,
    virtualSize: 0,
    coinbaseAddress: '',
    coinbaseAddresses: [],
    coinbaseSignature: '',
    coinbaseSignatureAscii: '',
  },
});

describe('RecentBlocksTable', () => {
  const blocks = [
    createMockBlock('abc1234567890', 1234, 1710000000),
    createMockBlock('def0987654321', 1233, 1700000000),
  ];

  it('renders header and block rows', () => {
    render(<RecentBlocksTable blocks={blocks} />);
    expect(screen.getByText(/latest blocks found/i)).toBeInTheDocument();

    // Check block rows
    expect(screen.getByText('1234')).toBeInTheDocument();
    expect(screen.getByText('short:abc1')).toBeInTheDocument();
    expect(screen.getByText('formatted:1710000000')).toBeInTheDocument();

    expect(screen.getByText('1233')).toBeInTheDocument();
    expect(screen.getByText('short:def0')).toBeInTheDocument();
    expect(screen.getByText('formatted:1700000000')).toBeInTheDocument();
  });

  it('opens and closes block dialog on row click', () => {
    render(<RecentBlocksTable blocks={blocks} />);

    const blockIdCell = screen.getByText('short:abc1');
    fireEvent.click(blockIdCell);

    expect(screen.getByTestId('block-dialog')).toBeInTheDocument();
    expect(
      screen.getByText(/block dialog: abc1234567890/i)
    ).toBeInTheDocument();

    const closeBtn = screen.getByText(/close/i);
    fireEvent.click(closeBtn);

    expect(screen.queryByTestId('block-dialog')).not.toBeInTheDocument();
  });

  it('respects maxHeight prop', () => {
    const { container } = render(
      <RecentBlocksTable blocks={blocks} maxHeight={200} />
    );
    const scrollContainer = container.querySelector('.overflow-auto');

    expect(scrollContainer).toHaveStyle('max-height: 200px');
  });
});
