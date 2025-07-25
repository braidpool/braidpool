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
    delete require.cache[require.resolve('../fetchHashrate')];
    delete require.cache[require.resolve('../rpcWithEnv')];

    ({ rpcWithEnv } = require('../rpcWithEnv'));
    ({ fetchHashrateStats } = require('../fetchHashrate'));

    mockClient = {
      readyState: 1,
      OPEN: 1,
      send: jest.fn(),
    };

    mockWSS = { clients: new Set([mockClient]) };

    rpcWithEnv.mockReset();

    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should fetch difficulty & hashrate then broadcast once', async () => {
    const diff = 65_000_000_000_000;
    const hashps = 500 * 1e18;
    const now = 1_752_000_000_000;

    jest.spyOn(Date, 'now').mockReturnValue(now);
    rpcWithEnv.mockResolvedValueOnce(diff).mockResolvedValueOnce(hashps);

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
        hashrate: hashps / 1e18,
        timestamp: now,
        networkDifficulty: diff,
      },
    });
  });

  it('should reuse cached difficulty within 30 s', async () => {
    const diff = 123456789;
    const t0 = 1_752_100_000_000;
    const t1 = t0 + 5_000;

    jest.spyOn(Date, 'now').mockReturnValueOnce(t0).mockReturnValueOnce(t1);

    rpcWithEnv
      .mockResolvedValueOnce(diff)
      .mockResolvedValueOnce(100 * 1e18)
      .mockResolvedValueOnce(200 * 1e18);

    await fetchHashrateStats(mockWSS);
    await fetchHashrateStats(mockWSS);

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
    jest.spyOn(Date, 'now').mockReturnValue(Date.now() + 100000);
    rpcWithEnv.mockRejectedValueOnce(new Error('RPC down'));

    await fetchHashrateStats(mockWSS);

    expect(console.error).toHaveBeenCalledWith(
      '[WebSocket] Failed to fetch or send hashrate stats:',
      'RPC down'
    );
    expect(mockClient.send).not.toHaveBeenCalled();
  });

  it('should not send when client is not OPEN', async () => {
    jest.spyOn(Date, 'now').mockReturnValue(Date.now() + 200000);
    mockClient.readyState = 2;
    mockClient.OPEN = 1;

    rpcWithEnv.mockResolvedValueOnce(8888).mockResolvedValueOnce(1e18);
    await fetchHashrateStats(mockWSS);
    expect(rpcWithEnv).toHaveBeenCalledTimes(2);
    expect(mockClient.send).not.toHaveBeenCalled();
  });
});
