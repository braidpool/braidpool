import React from 'react';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import '@testing-library/jest-dom';
import { MempoolData } from '../Types';

jest.mock('recharts', () => ({
  LineChart: ({
    children,
    data,
  }: {
    children: React.ReactNode;
    data: any[];
  }) => (
    <div data-testid="line-chart" data-chart-data={JSON.stringify(data)}>
      {children}
    </div>
  ),
  Line: ({
    dataKey,
    stroke,
    name,
    yAxisId,
  }: {
    dataKey: string;
    stroke: string;
    name: string;
    yAxisId: string;
  }) => (
    <div
      data-testid={`line-${dataKey}`}
      data-stroke={stroke}
      data-name={name}
      data-yaxis={yAxisId}
    />
  ),
  BarChart: ({
    children,
    data,
  }: {
    children: React.ReactNode;
    data: any[];
  }) => (
    <div data-testid="bar-chart" data-chart-data={JSON.stringify(data)}>
      {children}
    </div>
  ),
  Bar: ({ dataKey, fill }: { dataKey: string; fill: string }) => (
    <div data-testid={`bar-${dataKey}`} data-fill={fill} />
  ),
  XAxis: ({ dataKey, stroke }: { dataKey: string; stroke: string }) => (
    <div data-testid="x-axis" data-key={dataKey} data-stroke={stroke} />
  ),
  YAxis: ({
    stroke,
    yAxisId,
    orientation,
    label,
  }: {
    stroke: string;
    yAxisId?: string;
    orientation?: string;
    label?: { value: string; angle: number; position: string; fill: string };
  }) => (
    <div
      data-testid={`y-axis${yAxisId ? `-${yAxisId}` : ''}`}
      data-stroke={stroke}
      data-orientation={orientation}
      data-label={label?.value}
    />
  ),
  CartesianGrid: ({ stroke }: { strokeDasharray: string; stroke: string }) => (
    <div data-testid="cartesian-grid" data-stroke={stroke} />
  ),
  Tooltip: ({ contentStyle }: { contentStyle: React.CSSProperties }) => (
    <div data-testid="tooltip" data-style={JSON.stringify(contentStyle)} />
  ),
  Legend: () => <div data-testid="legend" />,
  ResponsiveContainer: ({
    children,
    width,
    height,
  }: {
    children: React.ReactNode;
    width: string | number;
    height: string | number;
  }) => (
    <div
      data-testid="responsive-container"
      data-width={width}
      data-height={height}
    >
      {children}
    </div>
  ),
}));

jest.mock(
  '../../theme/colors',
  () => ({
    primary: '#3b82f6',
    warning: '#f59e0b',
  }),
  { virtual: true }
);

jest.mock(
  '../../../theme/colors',
  () => ({
    primary: '#3b82f6',
    warning: '#f59e0b',
  }),
  { virtual: true }
);

interface MockWebSocketEventHandlers {
  onopen: ((event: Event) => void) | null;
  onclose: ((event: CloseEvent) => void) | null;
  onerror: ((event: Event) => void) | null;
  onmessage: ((event: MessageEvent) => void) | null;
}

class MockWebSocket implements WebSocket, MockWebSocketEventHandlers {
  readonly url: string;
  readyState: number;
  onopen: ((event: Event) => void) | null = null;
  onclose: ((event: CloseEvent) => void) | null = null;
  onerror: ((event: Event) => void) | null = null;
  onmessage: ((event: MessageEvent) => void) | null = null;

  readonly CONNECTING = 0;
  readonly OPEN = 1;
  readonly CLOSING = 2;
  readonly CLOSED = 3;
  binaryType: BinaryType = 'blob';
  bufferedAmount: number = 0;
  extensions: string = '';
  protocol: string = '';

  constructor(url: string) {
    this.url = url;
    this.readyState = WebSocket.CONNECTING;

    setTimeout(() => {
      this.readyState = WebSocket.OPEN;
      if (this.onopen) {
        this.onopen(new Event('open'));
      }
    }, 0);
  }

  close(code?: number, reason?: string): void {
    this.readyState = WebSocket.CLOSED;
    if (this.onclose) {
      this.onclose(new CloseEvent('close', { code, reason }));
    }
  }

  send(data: string | ArrayBufferLike | Blob | ArrayBufferView): void {}
  addEventListener(type: string, listener: EventListener): void {}
  removeEventListener(type: string, listener: EventListener): void {}
  dispatchEvent(event: Event): boolean {
    return true;
  }
}

(global as any).WebSocket = MockWebSocket;

const originalCreateElement = React.createElement;

const mockedCreateElement = (type: any, props: any, ...children: any[]) => {
  if (typeof type === 'function' && type.name === 'AnimatedStatCard') {
    return originalCreateElement('div', {
      'data-testid': `stat-card-${props?.title?.replace(/\s+/g, '-').toLowerCase() || 'unknown'}`,
      children: [
        originalCreateElement('div', { key: 'title' }, props?.title || ''),
        originalCreateElement('div', { key: 'value' }, props?.value || ''),
        props?.color &&
          originalCreateElement(
            'div',
            {
              key: 'color',
              'data-testid': 'card-color',
            },
            props.color
          ),
      ].filter(Boolean),
    });
  }

  return originalCreateElement(type, props, ...children);
};

(React as any).createElement = mockedCreateElement;

import MempoolLatencyStats from '../MempoolLatencyStats';

const mockMempoolData: MempoolData = {
  mempool: {
    vsize: 12345678,
    count: 50000,
    total_fee_btc: 1.23456789,
    total_fee_usd: 45000.5,
  },

  fees: {
    high_priority: {
      sats_per_vbyte: 30,
      fee_btc: 0.00012345,
      fee_usd: 4.5678,
    },
    medium_priority: {
      sats_per_vbyte: 20,
      fee_btc: 0.00008234,
      fee_usd: 3.0456,
    },
    standard_priority: {
      sats_per_vbyte: 15,
      fee_btc: 0.00006178,
      fee_usd: 2.2834,
    },
    economy: {
      sats_per_vbyte: 10,
      fee_btc: 0.00004123,
      fee_usd: 1.5267,
    },
  },
  fee_distribution: {
    '1-5': 1000,
    '5-10': 2500,
    '10-20': 5000,
    '20-30': 3000,
    '30+': 1500,
  },
  block_fee_history: [
    {
      time: '2023-01-01T12:00:00Z',
      btc: 0.5,
      usd: 18500,
    },
    {
      time: '2023-01-01T12:10:00Z',
      btc: 0.6,
      usd: 22200,
    },
  ],
};

const mockPartialData: Partial<MempoolData> = {
  mempool: {
    vsize: 5000000,
    count: 25000,
    total_fee_btc: 0.5,
    total_fee_usd: 18500,
  },
};

describe('MempoolLatencyStats', () => {
  let mockWebSocketInstance: MockWebSocket | null;

  beforeEach(() => {
    jest.clearAllMocks();
    mockWebSocketInstance = null;

    jest
      .spyOn(global as any, 'WebSocket')
      .mockImplementation((...args: unknown[]) => {
        const url = args[0] as string;
        mockWebSocketInstance = new MockWebSocket(url);
        return mockWebSocketInstance;
      });
  });

  afterEach(() => {
    jest.restoreAllMocks();
    (React as any).createElement = originalCreateElement;
  });

  describe('Initial Rendering', () => {
    test('renders loading state initially', () => {
      render(<MempoolLatencyStats />);
      expect(screen.getByText('Loading Mempool Stats...')).toBeInTheDocument();
    });

    test('does not render charts in loading state', () => {
      render(<MempoolLatencyStats />);
      expect(screen.queryByTestId('bar-chart')).not.toBeInTheDocument();
      expect(screen.queryByTestId('line-chart')).not.toBeInTheDocument();
    });
  });

  describe('WebSocket Connection', () => {
    test('establishes WebSocket connection on mount', () => {
      render(<MempoolLatencyStats />);
      expect((global as any).WebSocket).toHaveBeenCalledWith(
        'ws://localhost:5000'
      );
    });

    test('handles WebSocket connection opening', async () => {
      render(<MempoolLatencyStats />);

      await waitFor(() => {
        expect(mockWebSocketInstance?.readyState).toBe(WebSocket.OPEN);
      });
    });

    test('handles WebSocket errors gracefully', async () => {
      const consoleSpy = jest
        .spyOn(console, 'error')
        .mockImplementation(() => {});

      render(<MempoolLatencyStats />);

      await waitFor(() => {
        if (mockWebSocketInstance?.onerror) {
          const errorEvent = new Event('error');
          mockWebSocketInstance.onerror(errorEvent);
        }
      });

      expect(consoleSpy).toHaveBeenCalledWith(
        '[WebSocket] Error:',
        expect.any(Event)
      );
      consoleSpy.mockRestore();
    });

    test('cleans up WebSocket on unmount', () => {
      const { unmount } = render(<MempoolLatencyStats />);

      const closeSpy = jest.spyOn(
        mockWebSocketInstance as MockWebSocket,
        'close'
      );

      unmount();

      expect(closeSpy).toHaveBeenCalled();
    });
  });

  describe('Data Handling', () => {
    test('handles valid mempool data messages', async () => {
      render(<MempoolLatencyStats />);

      await waitFor(() => {
        if (mockWebSocketInstance?.onmessage) {
          const messageEvent = new MessageEvent('message', {
            data: JSON.stringify({
              type: 'mempool_update',
              data: mockMempoolData,
            }),
          });
          mockWebSocketInstance.onmessage(messageEvent);
        }
      });

      await waitFor(() => {
        expect(
          screen.queryByText('Loading Mempool Stats...')
        ).not.toBeInTheDocument();
      });
    });

    test('handles invalid JSON messages gracefully', async () => {
      const consoleSpy = jest
        .spyOn(console, 'error')
        .mockImplementation(() => {});

      render(<MempoolLatencyStats />);

      await waitFor(() => {
        if (mockWebSocketInstance?.onmessage) {
          const messageEvent = new MessageEvent('message', {
            data: 'invalid json',
          });
          mockWebSocketInstance.onmessage(messageEvent);
        }
      });

      expect(consoleSpy).toHaveBeenCalledWith(
        'WebSocket message parse error:',
        expect.any(Error)
      );
      consoleSpy.mockRestore();
    });

    test('handles messages with wrong type', async () => {
      render(<MempoolLatencyStats />);

      await waitFor(() => {
        if (mockWebSocketInstance?.onmessage) {
          const messageEvent = new MessageEvent('message', {
            data: JSON.stringify({
              type: 'other_update',
              data: mockMempoolData,
            }),
          });
          mockWebSocketInstance.onmessage(messageEvent);
        }
      });

      // Should still show loading state since it's not a mempool_update
      await waitFor(() => {
        expect(
          screen.getByText('Loading Mempool Stats...')
        ).toBeInTheDocument();
      });
    });

    test('handles partial or malformed data gracefully', async () => {
      render(<MempoolLatencyStats />);

      await waitFor(() => {
        if (mockWebSocketInstance?.onmessage) {
          const messageEvent = new MessageEvent('message', {
            data: JSON.stringify({
              type: 'mempool_update',
              data: mockPartialData,
            }),
          });
          mockWebSocketInstance.onmessage(messageEvent);
        }
      });

      // Component should handle partial data without crashing
      await waitFor(() => {
        expect(
          screen.queryByText('Loading Mempool Stats...')
        ).not.toBeInTheDocument();
      });
    });
  });

  describe('View Toggle Functionality', () => {
    beforeEach(async () => {
      render(<MempoolLatencyStats />);

      await waitFor(() => {
        if (mockWebSocketInstance?.onmessage) {
          const messageEvent = new MessageEvent('message', {
            data: JSON.stringify({
              type: 'mempool_update',
              data: mockMempoolData,
            }),
          });
          mockWebSocketInstance.onmessage(messageEvent);
        }
      });
    });

    test('renders view toggle buttons', async () => {
      await waitFor(() => {
        expect(screen.getByText('BTC')).toBeInTheDocument();
        expect(screen.getByText('USD')).toBeInTheDocument();
        expect(screen.getByText('BOTH')).toBeInTheDocument();
      });
    });

    test('BTC button toggles view correctly', async () => {
      const btcButton = screen.getByText('BTC');

      fireEvent.click(btcButton);

      await waitFor(() => {
        expect(btcButton).toHaveClass('bg-blue-600 text-white');
      });
    });

    test('USD button toggles view correctly', async () => {
      const usdButton = screen.getByText('USD');

      fireEvent.click(usdButton);

      await waitFor(() => {
        expect(usdButton).toHaveClass('bg-blue-600 text-white');
      });
    });

    test('BOTH button toggles view correctly', async () => {
      const bothButton = screen.getByText('BOTH');

      fireEvent.click(bothButton);

      await waitFor(() => {
        expect(bothButton).toHaveClass('bg-blue-600 text-white');
      });
    });
  });
});
