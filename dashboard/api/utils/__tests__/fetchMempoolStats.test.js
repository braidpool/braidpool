import axios from 'axios';
import {
  fetchMempoolStats,
  __resetBlockFeeCurrencyRateCache,
} from '../fetchMempoolStats';

jest.mock('axios');

const originalEnv = process.env;

beforeEach(() => {
  jest.resetAllMocks();
  __resetBlockFeeCurrencyRateCache();

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
  const FIAT_CURRENCY_COUNT = 12;

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
      .mockResolvedValueOnce({ data: mockBlockFeesData });

    for (let i = 0; i < FIAT_CURRENCY_COUNT; i += 1) {
      axios.get.mockResolvedValueOnce(mockCurrencyRates);
    }

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

  it('should continue when a currency rate API call fails', async () => {
    const consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation();

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData })
      .mockRejectedValueOnce(new Error('Currency API Error')); // First currency rate fails

    for (let i = 1; i < FIAT_CURRENCY_COUNT; i += 1) {
      axios.get.mockResolvedValueOnce(mockCurrencyRates);
    }

    const result = await fetchMempoolStats();

    expect(result).not.toBeNull();
    expect(result?.btc_price_usd).toBeUndefined();
    expect(result?.mempool.total_fee_usd).toBeUndefined();
    expect(result?.next_block_fees.fee_usd).toBeUndefined();
    expect(consoleErrorSpy).toHaveBeenCalledWith(
      '[getBlockFeeCurrencyRates] Failed to fetch USD; omitting currency: Currency API Error'
    );

    consoleErrorSpy.mockRestore();
  });

  it('should omit currencies with non-finite parsed rates', async () => {
    const consoleWarnSpy = jest.spyOn(console, 'warn').mockImplementation();

    axios.get
      .mockResolvedValueOnce({ data: mockStatsData })
      .mockResolvedValueOnce({ data: mockFeesData })
      .mockResolvedValueOnce({ data: mockOneMinuteBlockData })
      .mockResolvedValueOnce({ data: mockBlockFeesData })
      .mockResolvedValueOnce({ data: { data: { amount: 'not-a-number' } } }); // USD

    for (let i = 1; i < FIAT_CURRENCY_COUNT; i += 1) {
      axios.get.mockResolvedValueOnce(mockCurrencyRates);
    }

    const result = await fetchMempoolStats();

    expect(result).not.toBeNull();
    expect(result?.btc_price_usd).toBeUndefined();
    expect(result?.mempool.total_fee_usd).toBeUndefined();
    expect(result?.next_block_fees.fee_usd).toBeUndefined();
    expect(consoleWarnSpy).toHaveBeenCalledWith(
      '[getBlockFeeCurrencyRates] Non-finite rate for USD; omitting currency.'
    );

    consoleWarnSpy.mockRestore();
  });
});
