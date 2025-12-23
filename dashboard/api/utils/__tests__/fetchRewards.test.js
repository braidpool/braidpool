import axios from 'axios';
import { fetchReward } from '../fetchRewards.js';

jest.mock('axios');

describe('fetchReward', () => {
  const originalEnv = process.env.MEMPOOL_API_URL;
  beforeAll(() => {
    process.env.api_test = 'https://api_test.space';
  });
  afterAll(() => {
    process.env.api_test = originalEnv;
  });

  afterEach(() => {
    jest.clearAllMocks();
  });

  it('should not add duplicate blocks to history', async () => {
    axios.get.mockImplementation((url) => {
      if (url.includes('/api/blocks')) {
        return Promise.resolve({
          data: [
            {
              id: 'block123',
              height: 800000,
              timestamp: 1700000000,
            },
          ],
        });
      }
      if (url.includes('/api/block/block123/txs')) {
        return Promise.resolve({
          data: [
            {
              vout: [{ value: 625000000 }],
            },
          ],
        });
      }
      if (url.includes('coingecko.com')) {
        return Promise.resolve({
          data: {
            bitcoin: { usd: 45000 },
          },
        });
      }
      return Promise.reject(new Error('Unexpected URL'));
    });

    const firstResult = await fetchReward();
    const secondResult = await fetchReward();

    expect(firstResult).toHaveLength(1);
    expect(secondResult).toHaveLength(1);
    expect(firstResult[0].height).toBe(secondResult[0].height);
    expect(firstResult[0].height).toBe(800000);
  });

  it('should maintain maximum history length of 30 blocks', async () => {
    let blockCounter = 1;

    axios.get.mockImplementation((url) => {
      if (url.includes('/api/blocks')) {
        const currentBlock = {
          id: `block${blockCounter}`,
          height: 800000 + blockCounter,
          timestamp: 1700000000 + blockCounter,
        };
        return Promise.resolve({
          data: [currentBlock],
        });
      }
      if (url.includes('/api/block/')) {
        return Promise.resolve({
          data: [
            {
              vout: [{ value: 625000000 }],
            },
          ],
        });
      }
      if (url.includes('coingecko.com')) {
        return Promise.resolve({
          data: {
            bitcoin: { usd: 45000 },
          },
        });
      }
      return Promise.reject(new Error('Unexpected URL'));
    });

    let finalResult;
    for (let i = 1; i <= 32; i++) {
      blockCounter = i;
      finalResult = await fetchReward();
    }

    expect(finalResult).toHaveLength(30);

    // Should contain blocks 800003 to 800032 (latest 30)
    expect(finalResult[0].height).toBe(800003); // oldest kept
    expect(finalResult[29].height).toBe(800032); // newest
  });

  it('should handle API errors gracefully', async () => {
    axios.get.mockRejectedValueOnce(new Error('Network error'));

    const consoleSpy = jest
      .spyOn(console, 'error')
      .mockImplementation(() => {});

    const result = await fetchReward();

    expect(consoleSpy).toHaveBeenCalledWith(
      'Error fetching latest block reward:',
      'Network error'
    );
    // Should return the current (empty) history
    expect(Array.isArray(result)).toBe(true);

    consoleSpy.mockRestore();
  });

  it('should handle zero or empty vouts', async () => {
    axios.get.mockImplementation((url) => {
      if (url.includes('/api/blocks')) {
        return Promise.resolve({
          data: [
            {
              id: 'block789',
              height: 800002,
              timestamp: 1700000200,
            },
          ],
        });
      }
      if (url.includes('/api/block/block789/txs')) {
        return Promise.resolve({
          data: [
            {
              vout: [],
            },
          ],
        });
      }
      if (url.includes('coingecko.com')) {
        return Promise.resolve({
          data: {
            bitcoin: { usd: 40000 },
          },
        });
      }
      return Promise.reject(new Error('Unexpected URL'));
    });

    const result = await fetchReward();

    expect(result[result.length - 1]).toEqual({
      height: 800002,
      timestamp: new Date(1700000200 * 1000).toISOString(),
      rewardBTC: 0,
      rewardUSD: 0,
    });
  });
});
