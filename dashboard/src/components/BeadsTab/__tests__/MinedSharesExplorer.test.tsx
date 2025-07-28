import {
  render,
  screen,
  fireEvent,
  act,
  waitFor,
} from '@testing-library/react';
import MinedSharesExplorer from '../MinedSharesExplorer';

const mockBlockMessage = {
  type: 'block_data',
  data: {
    blockHash: 'hash123',
    height: 420,
    timestamp: new Date().toISOString(),
    work: '1.234 TH',
    txCount: 5,
    reward: 0.25555,
    parent: 'parent123',
    transactions: [
      {
        id: 'tx1',
        hash: 'txhash1',
        timestamp: new Date().toISOString(),
        count: 1,
        fee: 0.01,
        size: 200,
        feePaid: '0.01',
        feeRate: 5,
        inputs: 1,
        outputs: 2,
      },
    ],
  },
};

let mockWebSocketInstance: any;
let WebSocketMock: jest.Mock;

beforeAll(() => {
  mockWebSocketInstance = {
    onopen: null,
    onmessage: null,
    onerror: null,
    onclose: null,
    readyState: 1,
    close: jest.fn(),
    send: jest.fn(),
  };

  WebSocketMock = jest.fn(() => mockWebSocketInstance);
  global.WebSocket = WebSocketMock as any;
});

afterEach(() => {
  jest.clearAllMocks();
});

describe('<MinedSharesExplorer />', () => {
  it('shows loading state initially', () => {
    render(<MinedSharesExplorer />);
    expect(screen.getByText(/Connecting to server/i)).toBeInTheDocument();
  });

  it('renders bead after receiving WebSocket data', async () => {
    render(<MinedSharesExplorer />);
    const ws = WebSocketMock.mock.results[0].value;

    act(() => {
      ws.onopen?.();
      ws.onmessage?.({ data: JSON.stringify(mockBlockMessage) });
    });

    expect(await screen.findByText(/#420/i)).toBeInTheDocument();
    expect(screen.getByText(/255.55\s*mBTC/i)).toBeInTheDocument(); // match formatted reward
  });

  it('switches tabs correctly', async () => {
    render(<MinedSharesExplorer />);

    fireEvent.click(screen.getByRole('button', { name: /Rewards/i })); // avoid multiple matches

    await waitFor(() =>
      expect(screen.getByText(/Loading your rewards data/i)).toBeInTheDocument()
    );

    fireEvent.click(screen.getByRole('button', { name: /Bead Explorer/i }));
    expect(screen.getByText(/Bead Hash/i)).toBeInTheDocument();
  });

  it('handles pagination correctly', async () => {
    render(<MinedSharesExplorer />);
    const ws = WebSocketMock.mock.results[0].value;

    act(() => {
      ws.onopen?.();
      for (let i = 0; i < 7; i++) {
        const msg = {
          ...mockBlockMessage,
          data: {
            ...mockBlockMessage.data,
            blockHash: `hash${i}`,
            height: 420 + i,
          },
        };
        ws.onmessage?.({ data: JSON.stringify(msg) });
      }
    });

    expect(await screen.findByText(/#420/i)).toBeInTheDocument();
    expect(screen.getByText(/Page 1 of 2/i)).toBeInTheDocument();

    fireEvent.click(screen.getByText(/Next/i));
    expect(screen.getByText(/Page 2 of 2/i)).toBeInTheDocument();
  });

  it('toggles bead expansion correctly', async () => {
    render(<MinedSharesExplorer />);
    const ws = WebSocketMock.mock.results[0].value;

    act(() => {
      ws.onopen?.();
      ws.onmessage?.({ data: JSON.stringify(mockBlockMessage) });
    });

    const bead = await screen.findByText(/#420/i);
    fireEvent.click(bead);

    expect(screen.getByText(/txhash1/i)).toBeInTheDocument();
  });

  it('handles websocket error gracefully', async () => {
    render(<MinedSharesExplorer />);
    const ws = WebSocketMock.mock.results[0].value;

    act(() => {
      ws.onerror?.({ message: 'Connection failed' });
    });

    expect(screen.getByText(/Connecting to server/i)).toBeInTheDocument();
  });

  it('cleans up websocket on unmount', () => {
    const { unmount } = render(<MinedSharesExplorer />);
    const ws = WebSocketMock.mock.results[0].value;
    ws.close = jest.fn(); // ensure fresh mock

    unmount();

    expect(ws.close).toHaveBeenCalled(); // same ws reference
  });
});
