import WebSocket from 'ws';

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('fetchLatencyData', () => {
  let fetchLatencyData;
  let rpcWithEnv;
  let mockClient;
  let mockWSS;

  beforeAll(() => {
    WebSocket.CONNECTING = 0;
    WebSocket.OPEN = 1;
    WebSocket.CLOSING = 2;
    WebSocket.CLOSED = 3;
  });
  beforeEach(() => {
    jest.resetModules();
    ({ fetchLatencyData } = require('../fetchLatency'));
    ({ rpcWithEnv } = require('../rpcWithEnv'));

    mockClient = {
      readyState: WebSocket.OPEN,
      OPEN: WebSocket.OPEN,
      send: jest.fn(),
    };

    mockWSS = { clients: new Set([mockClient]) };

    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should broadcast latency data with valid pings', async () => {
    const now = 1_752_000_000_000;
    jest.spyOn(Date, 'now').mockReturnValue(now);

    rpcWithEnv.mockResolvedValue([
      { pingtime: 0.15 },
      { pingtime: 0.3 },
      { pingtime: 0.1 },
      { pingtime: null }, // ignored
      { pingtime: -1 }, // ignored
    ]);

    await fetchLatencyData(mockWSS);

    expect(mockClient.send).toHaveBeenCalledTimes(1);
    const payload = JSON.parse(mockClient.send.mock.calls[0][0]);

    expect(payload).toMatchObject({
      type: 'latency_data',
      data: {
        pings: [150, 300, 100],
        averageLatency: 183.33333333333334,
        peakLatency: 300,
        peerCount: 5,
        validPings: 3,
        timestamp: now,
      },
    });
  });

  it('should handle case with no valid pings gracefully', async () => {
    const now = 1_752_000_000_001;
    jest.spyOn(Date, 'now').mockReturnValue(now);

    rpcWithEnv.mockResolvedValue([
      { pingtime: null },
      { pingtime: -2 },
      { pingtime: 'fast' },
      { pingtime: 0 },
    ]);

    await fetchLatencyData(mockWSS);

    expect(console.warn).toHaveBeenCalledWith(
      '[LatencyStats] No valid pings to record.'
    );

    expect(mockClient.send).toHaveBeenCalledTimes(1);
    const payload = JSON.parse(mockClient.send.mock.calls[0][0]);

    expect(payload).toMatchObject({
      type: 'latency_data',
      data: {
        pings: [],
        averageLatency: 0,
        peakLatency: 0,
        peerCount: 4,
        validPings: 0,
        timestamp: now,
      },
    });
  });

  it('should not send if client is not OPEN', async () => {
    mockClient.readyState = WebSocket.CLOSING;

    rpcWithEnv.mockResolvedValue([{ pingtime: 0.12 }]);

    await fetchLatencyData(mockWSS);

    expect(mockClient.send).not.toHaveBeenCalled();
  });

  it('should log errors when RPC call fails', async () => {
    rpcWithEnv.mockRejectedValue(new Error('RPC crashed'));

    await fetchLatencyData(mockWSS);

    expect(console.error).toHaveBeenCalledWith(
      '[LatencyStats] Error:',
      'RPC crashed'
    );
  });
});
