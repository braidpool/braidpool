import { render, screen, act } from '@testing-library/react';
import NodeHealth from '../NodeHealth';

class WebSocketMock {
  static instances: WebSocketMock[] = [];
  private _readyState: number = WebSocket.CONNECTING; // Explicitly type as number

  constructor() {
    WebSocketMock.instances.push(this);
    setTimeout(() => {
      this._readyState = WebSocket.OPEN;
      this.onopen?.();
    }, 10);
  }

  get readyState(): number {
    return this._readyState;
  }
  onopen: (() => void) | null = null;
  onmessage: ((event: { data: string }) => void) | null = null;
  onerror: ((event: Event) => void) | null = null;
  onclose: (() => void) | null = null;

  send = jest.fn();
  close = jest.fn(() => {
    this._readyState = WebSocket.CLOSED;
    this.onclose?.();
  });
}

beforeAll(() => {
  global.WebSocket = WebSocketMock as any;
});

afterEach(() => {
  WebSocketMock.instances = [];
  jest.clearAllMocks();
});

const mockData = {
  type: 'node_health_data',
  data: {
    blockchainInfo: {
      blocks: 100,
      headers: 100,
      size_on_disk: 1073741824,
      bestblockhash: 'abcd1234efgh5678ijkl9012mnop3456qrst7890uvwx',
      chain: 'main',
      verificationprogress: 0.99,
      difficulty: 1234567,
      pruned: false,
    },
    peerInfo: [{ id: 1, addr: '127.0.0.1', subver: 'v0.1', pingtime: 0.1 }],
    networkInfo: {
      connections: 10,
      connections_in: 4,
      connections_out: 6,
    },
    mempoolInfo: {
      size: 5,
      usage: 1000000,
      maxmempool: 3000000,
    },
    netTotals: {
      totalbytesrecv: 1000,
      totalbytessent: 2000,
    },
    lastUpdated: new Date().toISOString(),
  },
};

describe('NodeHealth - WebSocket', () => {
  it('renders loading state initially', () => {
    render(<NodeHealth />);
    expect(screen.getByText(/Loading.../i)).toBeInTheDocument();
  });

  it('renders blockchain tab after receiving data', async () => {
    render(<NodeHealth />);
    const ws = WebSocketMock.instances[0];

    await act(async () => {
      ws.onmessage?.({ data: JSON.stringify(mockData) });
    });

    expect(screen.getByText(/block height/i)).toBeInTheDocument();
  });
  it('handles WebSocket error ', async () => {
    render(<NodeHealth />);
    const ws = WebSocketMock.instances[0];

    await act(() => {
      ws.onerror?.(new Event('error'));
    });
  });

  it('handles WebSocket close event', async () => {
    render(<NodeHealth />);
    const ws = WebSocketMock.instances[0];

    await act(() => {
      ws.close();
    });

    expect(ws.readyState).toBe(WebSocket.CLOSED);
  });

  it('switches tabs correctly', async () => {
    render(<NodeHealth />);
    const ws = WebSocketMock.instances[0];

    await act(async () => {
      ws.onmessage?.({ data: JSON.stringify(mockData) });
    });

    const peersTab = screen.getByText(/peers/i);
    await act(() => {
      peersTab.click();
    });

    expect(screen.getByText(/127.0.0.1/i)).toBeInTheDocument();
  });
});
