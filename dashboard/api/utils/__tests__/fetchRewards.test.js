const WebSocket = require('ws');
const { fetchReward } = require('../fetchRewards.js');
const { rpcWithEnv } = require('../rpcWithEnv.js');

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('fetchReward', () => {
  let fetchReward;
  let rpcWithEnv;
  let mockClient;
  let mockWSS;

  beforeEach(() => {
    jest.resetModules();
    ({ fetchReward } = require('../fetchRewards'));
    ({ rpcWithEnv } = require('../rpcWithEnv'));

    mockClient = {
      readyState: WebSocket.OPEN, // This should be 1
      send: jest.fn(),
    };
    mockWSS = { clients: new Set([mockClient]) };

    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.clearAllMocks();
  });

  it('should calculate and send reward data correctly', async () => {
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 735000, bestblockhash: 'abc123' }) // getblockchaininfo
      .mockResolvedValueOnce({ time: 1752000000 }); // getblock

    await fetchReward(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(2);
    expect(mockClient.send).toHaveBeenCalledTimes(1);

    const payload = JSON.parse(mockClient.send.mock.calls[0][0]);

    expect(payload.type).toBe('rewards_data');
    expect(payload.data.blockCount).toBe(735000);
    expect(payload.data.halvings).toBe(Math.floor(735000 / 210000));
    expect(payload.data.blockReward).toBe(
      50 / Math.pow(2, payload.data.halvings)
    );
    expect(payload.data.rewardRate).toBeCloseTo(payload.data.blockReward * 144);
    expect(payload.data.lastRewardTime).toBe(1752000000 * 1000);
    expect(payload.data.nextHalving).toBe((payload.data.halvings + 1) * 210000);
    expect(payload.data.blocksUntilHalving).toBe(
      payload.data.nextHalving - 735000
    );
    expect(payload.data.totalRewards).toBeGreaterThan(0);
  });

  it('should set lastRewardTime null if block fetch fails', async () => {
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100, bestblockhash: 'xyz999' }) // getblockchaininfo
      .mockRejectedValueOnce(new Error('Block not found')); // getblock fails

    await fetchReward(mockWSS);

    expect(console.warn).toHaveBeenCalledWith(
      '[Rewards] Could not fetch recent block info:',
      'Block not found'
    );

    const payload = JSON.parse(mockClient.send.mock.calls[0][0]);
    expect(payload.data.lastRewardTime).toBeNull();
  });

  it('currently sends to all clients', async () => {
    const openClient = {
      readyState: WebSocket.OPEN,
      send: jest.fn(),
    };

    const closingClient = {
      readyState: WebSocket.CLOSING,
      send: jest.fn(),
    };

    const closedClient = {
      readyState: WebSocket.CLOSED,
      send: jest.fn(),
    };

    const mockWSSWithMixedClients = {
      clients: new Set([openClient, closingClient, closedClient]),
    };

    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 210000, bestblockhash: 'abc123' })
      .mockResolvedValueOnce({ time: 1700000000 });

    await fetchReward(mockWSSWithMixedClients);

    expect(rpcWithEnv).toHaveBeenCalledTimes(2);

    expect(openClient.send).toHaveBeenCalledTimes(1);
    expect(closingClient.send).toHaveBeenCalledTimes(1);
    expect(closedClient.send).toHaveBeenCalledTimes(1);
  });

  it('should handle empty client set', async () => {
    const mockWSSWithNoClients = {
      clients: new Set(),
    };

    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 210000, bestblockhash: 'abc123' })
      .mockResolvedValueOnce({ time: 1700000000 });

    await fetchReward(mockWSSWithNoClients);

    expect(rpcWithEnv).toHaveBeenCalledTimes(2);
  });

  it('should log error if RPC completely fails', async () => {
    rpcWithEnv.mockRejectedValueOnce(new Error('RPC offline'));

    await fetchReward(mockWSS);

    expect(console.error).toHaveBeenCalledWith(
      '[Rewards] Failed to fetch/send reward data:',
      'RPC offline'
    );
    expect(mockClient.send).not.toHaveBeenCalled();
  });
});
