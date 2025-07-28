import axios from 'axios';
import fetchGlobalCryptoData from '../fetchGlobalData.js';

jest.mock('axios');

describe('fetchGlobalCryptoData', () => {
  const CRYPTO_URL = 'https://api.example.com/global';
  const currency = 'USD';

  const mockApiResponse = {
    data: {
      data: {
        quotes: {
          USD: {
            total_market_cap: 1000000000,
            total_market_cap_yesterday_percentage_change: 2.5,
          },
        },
        active_cryptocurrencies: 3000,
        active_markets: 500,
        bitcoin_percentage_of_market_cap: 48.7,
        last_updated: '2025-06-24T12:00:00Z',
      },
    },
  };

  it('should return structured global crypto data on success', async () => {
    axios.get.mockResolvedValue(mockApiResponse);

    const result = await fetchGlobalCryptoData(CRYPTO_URL, currency);

    expect(result).toEqual({
      marketCap: 1000000000,
      marketCapChange: 2.5,
      activeCryptocurrencies: 3000,
      activeMarkets: 500,
      bitcoinDominance: 48.7,
      lastUpdated: '2025-06-24T12:00:00Z',
    });

    expect(axios.get).toHaveBeenCalledWith(
      `${CRYPTO_URL}/?convert=${currency}`
    );
  });

  it('should return null and log error on failed request', async () => {
    axios.get.mockRejectedValueOnce(new Error('Network error'));

    const consoleSpy = jest
      .spyOn(console, 'error')
      .mockImplementation(() => {});

    const result = await fetchGlobalCryptoData(CRYPTO_URL, currency);

    expect(result).toBeNull();
    expect(consoleSpy).toHaveBeenCalledWith(
      'Error fetching global crypto data:',
      'Network error'
    );

    consoleSpy.mockRestore();
  });

  it('should return null and log error on malformed response', async () => {
    axios.get.mockResolvedValue({ data: {} }); // missing `data.data`
    const consoleSpy = jest
      .spyOn(console, 'error')
      .mockImplementation(() => {});
    const result = await fetchGlobalCryptoData(CRYPTO_URL, currency);
    expect(result).toBeNull();
    expect(consoleSpy).toHaveBeenCalledWith(
      'Error fetching global crypto data:',
      'Invalid response format'
    );
    consoleSpy.mockRestore();
  });
});
