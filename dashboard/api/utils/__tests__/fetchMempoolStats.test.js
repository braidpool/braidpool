import axios from 'axios';
import { fetchMempoolStats } from '../fetchMempoolStats';

jest.mock('axios');

const originalEnv = process.env;

beforeEach(() => {
  jest.resetAllMocks();

  process.env = {
    ...originalEnv,
    MEMPOOL_STATS_URL: 'https://api.test.com',
    FEE_RECOMMENDED_URL: 'https://api.test.com/api/v1/fees/recommended',
    BTC_PRICE_URL: 'https://api.test.com/v1/api/currentprice/USD.json',
    ONE_MIN_BLOCK_FEE_URL: 'https://api.test.com/api/v1/mining/blocks/fees/1m',
    BLOCK_FEES_HISTORY_URL:
      'https://api.test.com/api/v1/mining/blocks/fees/24h',
  };
});

afterEach(() => {
  process.env = originalEnv;
});

describe('fetchMempoolStats', () => {
  const mockStatsData = {
    count: 5000,
    vsize: 2500000,
    total_fee: 50000000, // 0.5 BTC in satoshis
  };

  const mockFeesData = {
    fastestFee: 20,
    halfHourFee: 15,
    hourFee: 10,
    economyFee: 5,
    minimumFee: 1,
  };

  const mockPriceData = {
    price: '45000.50',
  };

  const mockOneMinuteBlockData = [
    {
      avgFee_0: 1,
      avgFee_10: 5,
      avgFee_25: 8,
      avgFee_50: 12,
      avgFee_75: 18,
      avgFee_90: 25,
      avgFee_100: 50,
    },
  ];

  const mockBlockFeesData = [
    {
      avgHeight: 800000,
      timestamp: 1640995200, // Jan 1, 2022 00:00:00 UTC
      avgFees: 25000000, // 0.25 BTC in satoshis
      USD: 11250.25,
    },
  ];

  it('should handle empty one minute block data array', async () => {
    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: [] }) // Empty array
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    const result = await fetchMempoolStats();

    expect(result?.fee_distribution).toEqual({
      min: undefined,
      '10th': undefined,
      '25th': undefined,
      median: undefined,
      '75th': undefined,
      '90th': undefined,
      max: undefined,
    });
  });

  it('should handle non-array one minute block data', async () => {
    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: null }) // Non-array data
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    const result = await fetchMempoolStats();

    expect(result?.fee_distribution).toEqual({
      min: undefined,
      '10th': undefined,
      '25th': undefined,
      median: undefined,
      '75th': undefined,
      '90th': undefined,
      max: undefined,
    });
  });

  it('should handle empty block fees history array', async () => {
    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: [] }); // Empty array

    const result = await fetchMempoolStats();

    expect(result?.block_fee_history).toEqual([]);
  });

  it('should handle non-array block fees history data', async () => {
    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: null }); // Non-array data

    const result = await fetchMempoolStats();

    expect(result?.block_fee_history).toEqual([]);
  });

  it('should handle missing timestamp in block fees data', async () => {
    const mockBlockFeesDataNoTimestamp = [
      {
        avgHeight: 800000,
        // timestamp missing
        avgFees: 25000000,
        USD: 11250.25,
      },
    ];

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesDataNoTimestamp });

    const result = await fetchMempoolStats();

    expect(result?.block_fee_history[0].time).toBe(
      new Date(0).toLocaleTimeString()
    );
  });

  it('should handle zero BTC price', async () => {
    const mockZeroPriceData = { price: '0' };

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockZeroPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    const result = await fetchMempoolStats();

    expect(result?.btc_price_usd).toBe(0);
    expect(result?.mempool.total_fee_usd).toBe(0);
    expect(result?.fees.high_priority.fee_usd).toBe(0);
  });

  it('should handle network error and return null', async () => {
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation();

    axios.get.mockRejectedValueOnce(new Error('Network Error'));

    const result = await fetchMempoolStats();

    expect(result).toBeNull();
    expect(consoleErrorSpy).toHaveBeenCalledWith(
      '[fetchMempoolStats] Failed to fetch:',
      'Network Error'
    );

    consoleErrorSpy.mockRestore();
  });

  it('should handle partial API failures and return null', async () => {
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation();

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockRejectedValueOnce(new Error('Price API Error'));

    const result = await fetchMempoolStats();

    expect(result).toBeNull();
    expect(consoleErrorSpy).toHaveBeenCalledWith(
      '[fetchMempoolStats] Failed to fetch:',
      'Price API Error'
    );

    consoleErrorSpy.mockRestore();
  });

  it('should handle invalid price data', async () => {
    const mockInvalidPriceData = { price: 'invalid' };

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockInvalidPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    const result = await fetchMempoolStats();

    expect(result?.btc_price_usd).toBeNaN();
    expect(result?.mempool.total_fee_usd).toBeNaN();
  });

  it('should log console messages correctly', async () => {
    const consoleLogSpy = jest.spyOn(console, 'log').mockImplementation();

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    await fetchMempoolStats();

    expect(consoleLogSpy).toHaveBeenCalledWith(
      '[blockfeesRes.data sample]',
      mockBlockFeesData[0]
    );
    expect(consoleLogSpy).toHaveBeenCalledWith('[btcPriceUSD]', 45000.5);

    consoleLogSpy.mockRestore();
  });

  it('should correctly convert fees from satoshis to BTC and USD', async () => {
    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockPriceData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    const result = await fetchMempoolStats();
    const fastestFeeResult = result?.fees.high_priority;
    expect(fastestFeeResult?.sats_per_vbyte).toBe(20);
    expect(fastestFeeResult?.fee_btc).toBe(20 / 1e8);
    expect(fastestFeeResult?.fee_usd).toBe((20 / 1e8) * 45000.5);
  });
});
