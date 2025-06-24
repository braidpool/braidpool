import '@testing-library/jest-dom';
import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import BlockViewer from '../BlockViewer';
import * as Utils from '../Utils';
import { Block } from '../Types';

// Mock WebSocket for testing
const originalWebSocket = global.WebSocket;

class MockWebSocket {
  onopen: Function = () => {};
  onmessage: Function = () => {};
  onerror: Function = () => {};
  onclose: Function = () => {};
  close = jest.fn();
  send = jest.fn();
  readyState = 1;
  url: string;

  constructor(url: string) {
    if (
      !url.startsWith('ws://') &&
      !url.startsWith('wss://') &&
      !url.startsWith('http://') &&
      !url.startsWith('https://')
    ) {
      throw new SyntaxError('Invalid WebSocket URL');
    }
    this.url = url;
    setTimeout(() => this.onopen({}), 10); // Simulate connection open
  }
}

global.WebSocket = MockWebSocket as any;

jest.mock('../RecentBlocksTable', () => () => (
  <div data-testid="recent-blocks-table" />
));
jest.mock('../BlockDialog', () => ({ hash, onClose }: any) => (
  <div data-testid="block-dialog">
    Block Dialog: {hash}
    <button onClick={onClose}>Close</button>
  </div>
));

jest.mock('../../../theme/colors', () => ({
  primary: '#ff0000',
  paper: '#121212',
}));

describe('BlockViewer Component', () => {
  const createMockBlock = (id: string, height: number): Block => ({
    id,
    height,
    version: 1,
    timestamp: Date.now(),
    bits: 0,
    nonce: 0,
    difficulty: 0,
    merkle_root: '',
    tx_count: 100,
    size: 1000,
    weight: 2000,
    previousblockhash: 'prev',
    mediantime: Date.now(),
    stale: false,
    extras: {
      reward: 625000000,
      coinbaseRaw: '',
      orphans: [],
      medianFee: 12,
      feeRange: [10, 20, 15],
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

  const mockBlocks = [
    createMockBlock('abc123', 12345),
    createMockBlock('def456', 12344),
  ];

  beforeEach(() => {
    jest.spyOn(Utils, 'fetchPreviousBlocks').mockResolvedValue(mockBlocks);
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  afterAll(() => {
    global.WebSocket = originalWebSocket;
  });

  it('shows loading state initially', async () => {
    render(<BlockViewer />);
    expect(screen.getByText(/loading blocks/i)).toBeInTheDocument();
    await waitFor(() =>
      expect(screen.queryByText(/loading blocks/i)).not.toBeInTheDocument()
    );
  });

  it('displays fetched blocks after loading', async () => {
    render(<BlockViewer />);
    await waitFor(() => {
      expect(screen.getByText(/block explorer/i)).toBeInTheDocument();
      expect(screen.getByTestId('recent-blocks-table')).toBeInTheDocument();
    });
  });

  it('shows "No blocks available" if fetch returns empty array', async () => {
    (Utils.fetchPreviousBlocks as jest.Mock).mockResolvedValue([]);
    render(<BlockViewer />);
    await waitFor(() => {
      expect(screen.getByText(/no blocks available/i)).toBeInTheDocument();
    });
  });

  it('opens block dialog when a block is clicked', async () => {
    render(<BlockViewer />);
    await waitFor(() => screen.getByText(/block explorer/i));
    const blockCard = screen.getAllByText(/txs/i)[0];
    fireEvent.click(blockCard);
    expect(await screen.findByTestId('block-dialog')).toBeInTheDocument();
    fireEvent.click(screen.getByText(/close/i));
    expect(screen.queryByTestId('block-dialog')).not.toBeInTheDocument();
  });

  it('shows WebSocket connected status', async () => {
    render(<BlockViewer />);
    await waitFor(() =>
      expect(screen.getByText(/connected/i)).toBeInTheDocument()
    );
  });

  it('shows WebSocket disconnected on error', async () => {
    class ErrorMockWebSocket extends MockWebSocket {
      constructor(url: string) {
        super(url);
        setTimeout(() => this.onerror(new Event('error')), 10);
      }
    }

    global.WebSocket = ErrorMockWebSocket as any;

    render(<BlockViewer />);
    await waitFor(() =>
      expect(screen.getByText(/disconnected/i)).toBeInTheDocument()
    );
  });

  it('processes new block from WebSocket message', async () => {
    class MessageMockWebSocket extends MockWebSocket {
      constructor(url: string) {
        super(url);
        setTimeout(() => {
          this.onmessage({
            data: JSON.stringify({
              block: createMockBlock('ws-new-block', 12346),
            }),
          });
        }, 20);
      }
    }

    global.WebSocket = MessageMockWebSocket as any;

    render(<BlockViewer />);
    await waitFor(() => {
      expect(screen.getByText(/connected/i)).toBeInTheDocument();
      expect(screen.getByTestId('recent-blocks-table')).toBeInTheDocument();
    });
  });
});
