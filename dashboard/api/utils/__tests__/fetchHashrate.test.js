import WebSocket from 'ws';

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('fetchHashrateStats (difficulty)', () => {
  let fetchHashrateStats;
  let rpcWithEnv;
  let mockClient;
  let mockWSS;

  beforeEach(() => {
    jest.resetModules();
    ({ rpcWithEnv } = require('../rpcWithEnv'));
    ({ fetchHashrateStats } = require('../fetchHashrate'));

    mockClient = {
      readyState: WebSocket.OPEN, // 1
      OPEN: WebSocket.OPEN, // 1 – required by code under test
      send: jest.fn(),
    };
    mockWSS = { clients: new Set([mockClient]) };

    rpcWithEnv.mockReset();

    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('broadcasts only the network difficulty, in T', async () => {
    const diff = 65_000_000_000_000;
    const now = 1_752_000_000_000;

    jest.spyOn(Date, 'now').mockReturnValue(now);
    rpcWithEnv.mockResolvedValueOnce(diff);

    await fetchHashrateStats(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(1);
    expect(rpcWithEnv).toHaveBeenCalledWith({ method: 'getdifficulty' });

    expect(mockClient.send).toHaveBeenCalledTimes(1);
    const payload = JSON.parse(mockClient.send.mock.calls[0][0]);
    expect(payload).toEqual({
      type: 'hashrate_data',
      data: {
        networkDifficulty: diff / 1e12,
        timestamp: now,
      },
    });
    expect(payload.data).not.toHaveProperty('hashrate');
  });

  it('reuses cached difficulty within 30 s', async () => {
    const diff = 123456789;
    const t0 = 1_752_100_000_000;
    const t1 = t0 + 5_000;

    jest.spyOn(Date, 'now').mockReturnValueOnce(t0).mockReturnValueOnce(t1);

    rpcWithEnv.mockResolvedValueOnce(diff);

    await fetchHashrateStats(mockWSS);
    await fetchHashrateStats(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(1);
    expect(mockClient.send).toHaveBeenCalledTimes(2);
  });

  it('refetches difficulty after the 30 s cache expires', async () => {
    const t0 = 1_752_100_000_000;
    const t1 = t0 + 31_000;

    jest.spyOn(Date, 'now').mockReturnValueOnce(t0).mockReturnValueOnce(t1);

    rpcWithEnv.mockResolvedValueOnce(100).mockResolvedValueOnce(200);

    await fetchHashrateStats(mockWSS);
    await fetchHashrateStats(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(2);
  });

  it('logs and skips sending on RPC failure', async () => {
    rpcWithEnv.mockRejectedValueOnce(new Error('RPC down'));

    await fetchHashrateStats(mockWSS);

    expect(console.error).toHaveBeenCalledWith(
      '[WebSocket] Failed to fetch or send difficulty:',
      'RPC down'
    );
    expect(mockClient.send).not.toHaveBeenCalled();
  });

  it('does not send to clients that are not OPEN', async () => {
    mockWSS.clients = new Set();
    rpcWithEnv.mockResolvedValueOnce(65_000_000_000_000);

    await fetchHashrateStats(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(1);
    expect(mockClient.send).not.toHaveBeenCalled();
  });
});
