import axios from 'axios';
import fetchBitcoinPrices from '../fetchBitcoinPrices.js';

jest.mock('axios');

describe('fetchBitcoinPrices', () => {
  const BASE_URL = 'https://api.test.com/price?currency=';
  const SUFFIX = '&format=json';

  afterEach(() => {
    jest.clearAllMocks();
  });

  it('should fetch BTC prices for USD, EUR, and JPY with correct high and low values', async () => {
    axios.get.mockImplementation((url) => {
      if (url.includes('USD') && url.includes(SUFFIX)) {
        return Promise.resolve({ data: { data: { amount: '30000' } } });
      }
      if (url.includes('USD') && url.includes('/historic')) {
        return Promise.resolve({
          data: {
            data: {
              prices: [
                { price: '29000' },
                { price: '31000' },
                { price: '30500' },
              ],
            },
          },
        });
      }

      if (url.includes('EUR') && url.includes(SUFFIX)) {
        return Promise.resolve({ data: { data: { amount: '28000' } } });
      }
      if (url.includes('EUR') && url.includes('/historic')) {
        return Promise.resolve({
          data: {
            data: {
              prices: [
                { price: '27000' },
                { price: '28500' },
                { price: '27500' },
              ],
            },
          },
        });
      }

      if (url.includes('JPY') && url.includes(SUFFIX)) {
        return Promise.resolve({ data: { data: { amount: '4000000' } } });
      }
      if (url.includes('JPY') && url.includes('/historic')) {
        return Promise.resolve({
          data: {
            data: {
              prices: [
                { price: '3900000' },
                { price: '4050000' },
                { price: '3950000' },
              ],
            },
          },
        });
      }

      return Promise.reject(new Error('Unexpected URL'));
    });

    const result = await fetchBitcoinPrices(BASE_URL, SUFFIX);

    expect(result).toEqual({
      USD: {
        current: 30000,
        high24h: 31000,
        low24h: 29000,
      },
      EUR: {
        current: 28000,
        high24h: 28500,
        low24h: 27000,
      },
      JPY: {
        current: 4000000,
        high24h: 4050000,
        low24h: 3900000,
      },
    });

    // 6 total calls: 3 spot + 3 historic
    expect(axios.get).toHaveBeenCalledTimes(6);
  });

  it('should return null and log error if one request fails', async () => {
    axios.get.mockRejectedValueOnce(new Error('Fail'));

    const consoleSpy = jest
      .spyOn(console, 'error')
      .mockImplementation(() => {});

    const result = await fetchBitcoinPrices(BASE_URL, SUFFIX);

    expect(result).toBeNull();
    expect(consoleSpy).toHaveBeenCalledWith(
      'Error fetching BTC price data:',
      'Fail'
    );

    consoleSpy.mockRestore();
  });
});
