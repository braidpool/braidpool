import axios from 'axios';
import { fetchMempoolStats } from '../fetchMempoolStats';

jest.mock('axios');

const originalEnv = process.env;

beforeEach(() => {
  jest.resetAllMocks();

  process.env = {
    ...originalEnv,
    MEMPOOL_URL: 'https://mempool.space',
    BITCOIN_PRICE_URL:
      'https://api.coinbase.com/v2/exchange-rates?currency=BTC&rates=',
    BITCOIN_PRICE_URL_SUFFIX: '',
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

  const mockBinancePriceData = {
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

  const mockCurrencyRates = {
    data: {
      data: {
        amount: '45000.50',
      },
    },
  };

  it('should handle empty one minute block data array', async () => {
    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: [] }) // Empty array
      .mockResolvedValueOnce({ data: mockBlockFeesData })
      .mockResolvedValueOnce(mockCurrencyRates) // USD
      .mockResolvedValueOnce(mockCurrencyRates) // EUR
      .mockResolvedValueOnce(mockCurrencyRates); // JPY

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

  it('should handle currency rate API failure', async () => {
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation();

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData })
      .mockRejectedValueOnce(new Error('Currency API Error')); // USD rate fails

    const result = await fetchMempoolStats();

    expect(result).toBeNull();
    expect(consoleErrorSpy).toHaveBeenCalledWith(
      '[fetchMempoolStats] Failed to fetch:',
      'Currency API Error'
    );

    consoleErrorSpy.mockRestore();
  });
});
