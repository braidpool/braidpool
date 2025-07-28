import WebSocket from 'ws';

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('fetchHashrateStats', () => {
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

    // 3️⃣ keep console output quiet
    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should fetch difficulty & hashrate then broadcast once', async () => {
    const diff = 65_000_000_000_000;
    const hashps = 500 * 1e18; // 500 EH/s
    const now = 1_752_000_000_000; // fake timestamp

    jest.spyOn(Date, 'now').mockReturnValue(now);
    rpcWithEnv
      .mockResolvedValueOnce(diff) // getdifficulty
      .mockResolvedValueOnce(hashps); // getnetworkhashps

    await fetchHashrateStats(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(2);
    expect(
      rpcWithEnv.mock.calls.some((call) => call[0].method === 'getdifficulty')
    ).toBe(true);

    expect(mockClient.send).toHaveBeenCalledTimes(1);
    const payload = JSON.parse(mockClient.send.mock.calls[0][0]);
    expect(payload).toMatchObject({
      type: 'hashrate_data',
      data: {
        hashrate: hashps / 1e18, // EH/s
        timestamp: now,
        networkDifficulty: diff,
      },
    });
  });

  it('should reuse cached difficulty within 30 s', async () => {
    const diff = 123456789;
    const t0 = 1_752_100_000_000; // first call
    const t1 = t0 + 5_000; // second call ( < 30 s)

    jest
      .spyOn(Date, 'now')
      .mockReturnValueOnce(t0) // for first fetch
      .mockReturnValueOnce(t1); // for second fetch

    rpcWithEnv
      .mockResolvedValueOnce(diff) // getdifficulty (1×)
      .mockResolvedValueOnce(100 * 1e18) // hashps 1
      .mockResolvedValueOnce(200 * 1e18); // hashps 2

    await fetchHashrateStats(mockWSS); // first call
    await fetchHashrateStats(mockWSS); // second call

    // exactly one difficulty query, two networkhashps queries
    expect(
      rpcWithEnv.mock.calls.filter((c) => c[0].method === 'getdifficulty')
    ).toHaveLength(1);
    expect(
      rpcWithEnv.mock.calls.filter((c) => c[0].method === 'getnetworkhashps')
    ).toHaveLength(2);

    expect(mockClient.send).toHaveBeenCalledTimes(2);
    const firstDiff = JSON.parse(mockClient.send.mock.calls[0][0]).data
      .networkDifficulty;
    const secondDiff = JSON.parse(mockClient.send.mock.calls[1][0]).data
      .networkDifficulty;
    expect(firstDiff).toBe(diff);
    expect(secondDiff).toBe(diff);
  });

  it('should log & skip send on RPC failure', async () => {
    rpcWithEnv.mockRejectedValueOnce(new Error('RPC down'));

    await fetchHashrateStats(mockWSS);

    expect(console.error).toHaveBeenCalledWith(
      '[WebSocket] Failed to fetch or send hashrate stats:',
      'RPC down'
    );
    expect(mockClient.send).not.toHaveBeenCalled();
  });

  it('should not send when client is not OPEN', async () => {
    const diff = 65_000_000_000_000;
    const hashps = 500 * 1e18;

    mockWSS.clients = new Set();

    rpcWithEnv
      .mockResolvedValueOnce(diff) // getdifficulty
      .mockResolvedValueOnce(hashps); // getnetworkhashps

    await fetchHashrateStats(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(2);
    expect(mockClient.send).not.toHaveBeenCalled();
  });
});
