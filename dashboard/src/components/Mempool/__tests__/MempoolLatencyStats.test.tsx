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

jest.mock(
  '../Constants',
  () => ({
    currencyLabels: {
      btc: 'BTC',
      usd: 'USD',
      eur: 'EUR',
      jpy: 'JPY',
    },
    currencyColors: {
      btc: '#f7931a',
      usd: '#4ade80',
      eur: '#3b82f6',
      jpy: '#ef4444',
    },
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
    total_fee_eur: 42000.0,
    total_fee_jpy: 5000000,
  },
  next_block_fees: {
    sats_per_vbyte: 25,
    fee_btc: 0.00010345,
    fee_usd: 3.8901,
    fee_eur: 3.6234,
    fee_jpy: 420.5,
  },
  fees: {
    high_priority: {
      sats_per_vbyte: 30,
      fee_btc: 0.00012345,
      fee_usd: 4.5678,
      fee_eur: 4.2567,
      fee_jpy: 460.8,
    },
    medium_priority: {
      sats_per_vbyte: 20,
      fee_btc: 0.00008234,
      fee_usd: 3.0456,
      fee_eur: 2.8401,
      fee_jpy: 307.2,
    },
    standard_priority: {
      sats_per_vbyte: 15,
      fee_btc: 0.00006178,
      fee_usd: 2.2834,
      fee_eur: 2.1301,
      fee_jpy: 230.4,
    },
    economy: {
      sats_per_vbyte: 10,
      fee_btc: 0.00004123,
      fee_usd: 1.5267,
      fee_eur: 1.4234,
      fee_jpy: 153.6,
    },
    minimum: {
      sats_per_vbyte: 5,
      fee_btc: 0.00002061,
      fee_usd: 0.7634,
      fee_eur: 0.7117,
      fee_jpy: 76.8,
    },
  },
  currency_rates: {
    USD: 37000,
    EUR: 34500,
    JPY: 4000000,
  },
  fee_distribution: {
    min: 5,
    '10th': 8,
    '25th': 12,
    median: 18,
    '75th': 25,
    '90th': 35,
    max: 50,
  },
  block_fee_history: [
    {
      height: 908901,
      time: '1:25:15 AM',
      timestamp: 1754510115,
      btc: 0.5,
      usd: 18500,
      eur: 17250,
      jpy: 2000000,
    },
    {
      height: 908902,
      time: '1:28:22 AM',
      timestamp: 1754510302,
      btc: 0.6,
      usd: 22200,
      eur: 20700,
      jpy: 2400000,
    },
  ],
};

const mockPartialData: Partial<MempoolData> = {
  mempool: {
    vsize: 5000000,
    count: 25000,
    total_fee_btc: 0.5,
    total_fee_usd: 18500,
    total_fee_eur: 17250,
    total_fee_jpy: 2000000,
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

    test('renders currency select dropdown', async () => {
      await waitFor(() => {
        const selectElement = screen.getByRole('combobox');
        expect(selectElement).toBeInTheDocument();
        expect(selectElement).toHaveValue('all');
      });
    });

    test('contains all currency options in dropdown', async () => {
      await waitFor(() => {
        expect(screen.getByDisplayValue('ALL')).toBeInTheDocument();
      });

      const selectElement = screen.getByRole('combobox');

      // Check all options exist
      const options = selectElement.querySelectorAll('option');
      const optionValues = Array.from(options).map((option) =>
        option.getAttribute('value')
      );

      expect(optionValues).toContain('btc');
      expect(optionValues).toContain('usd');
      expect(optionValues).toContain('eur');
      expect(optionValues).toContain('jpy');
      expect(optionValues).toContain('all');
    });

    test('changes view when selecting different currency', async () => {
      await waitFor(() => {
        const selectElement = screen.getByRole('combobox');
        fireEvent.change(selectElement, { target: { value: 'usd' } });
        expect(selectElement).toHaveValue('usd');
      });
    });

    test('defaults to "all" view initially', async () => {
      await waitFor(() => {
        const selectElement = screen.getByRole('combobox');
        expect(selectElement).toHaveValue('all');
      });
    });
  });

  describe('Component Rendering with Data', () => {
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
    test('renders fee distribution chart', async () => {
      await waitFor(() => {
        expect(
          screen.getByText('Live Fee Rate Distribution')
        ).toBeInTheDocument();
        expect(screen.getByTestId('bar-chart')).toBeInTheDocument();
      });
    });

    test('renders block fee chart', async () => {
      await waitFor(() => {
        expect(screen.getByText('Live Block Fees')).toBeInTheDocument();
        expect(screen.getByTestId('line-chart')).toBeInTheDocument();
      });
    });
  });
});
