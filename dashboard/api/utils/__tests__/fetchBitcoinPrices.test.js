import axios from 'axios';
import fetchBitcoinPrices from '../fetchBitcoinPrices.js';

// Mocking axios for tessting
jest.mock('axios');

describe('fetchBitcoinPrices', () => {
  const BASE_URL = 'https://api.test.com/price?currency=';
  const SUFFIX = '&format=json';

  it('should fetch BTC prices for USD, EUR, and JPY', async () => {
    axios.get.mockImplementation((url) => {
      if (url.includes('USD'))
        return Promise.resolve({ data: { data: { amount: '30000' } } });
      if (url.includes('EUR'))
        return Promise.resolve({ data: { data: { amount: '28000' } } });
      if (url.includes('JPY'))
        return Promise.resolve({ data: { data: { amount: '4000000' } } });
    });

    const prices = await fetchBitcoinPrices(BASE_URL, SUFFIX);

    expect(prices).toEqual({
      USD: '30000',
      EUR: '28000',
      JPY: '4000000',
    });

    expect(axios.get).toHaveBeenCalledTimes(3);
  });

  it('should return null and log error if one request fails', async () => {
    axios.get.mockRejectedValueOnce(new Error('Fail'));

    const consoleSpy = jest
      .spyOn(console, 'error')
      .mockImplementation(() => {});

    const result = await fetchBitcoinPrices(BASE_URL, SUFFIX);

    expect(result).toBeNull();
    expect(consoleSpy).toHaveBeenCalledWith(
      'Error fetching BTC price:',
      'Fail'
    );

    consoleSpy.mockRestore();
  });
});
