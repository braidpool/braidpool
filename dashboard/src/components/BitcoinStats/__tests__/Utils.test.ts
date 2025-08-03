import axios from 'axios';
import {
  getCurrencySymbol,
  formatPrice,
  formatLargeNumber,
  shortenAddress,
  getLatestTransactions,
  getTxInfo,
} from '../Utils';
import { getMempoolRecentUrl, getMempoolTransactionUrl } from '../../../URLs';

jest.mock('axios');
const mockedAxios = axios as jest.Mocked<typeof axios>;

describe('Utility Functions', () => {
  describe('getCurrencySymbol', () => {
    it('returns correct symbol for EUR', () => {
      expect(getCurrencySymbol('EUR')).toBe('€');
    });
    it('returns correct symbol for GBP', () => {
      expect(getCurrencySymbol('GBP')).toBe('£');
    });
    it('returns correct symbol for JPY', () => {
      expect(getCurrencySymbol('JPY')).toBe('¥');
    });
    it('returns $ for unknown currency', () => {
      expect(getCurrencySymbol('USD')).toBe('$');
      expect(getCurrencySymbol('')).toBe('$');
    });
  });

  describe('formatPrice', () => {
    it('formats numbers to 2 decimal places', () => {
      expect(formatPrice(1234.5678)).toBe('1,234.57');
      expect(formatPrice(0)).toBe('--');
      expect(formatPrice(NaN)).toBe('--');
    });
  });

  describe('formatLargeNumber', () => {
    it('returns "--" for falsy values', () => {
      expect(formatLargeNumber(0)).toBe('--');
      expect(formatLargeNumber(NaN)).toBe('--');
    });

    it('formats trillions with T suffix', () => {
      expect(formatLargeNumber(1e12)).toBe('1.00T');
      expect(formatLargeNumber(2.345e12)).toBe('2.35T');
    });

    it('formats billions with B suffix', () => {
      expect(formatLargeNumber(1e9)).toBe('1.00B');
      expect(formatLargeNumber(5.678e9)).toBe('5.68B');
    });

    it('formats millions with M suffix', () => {
      expect(formatLargeNumber(1e6)).toBe('1.00M');
      expect(formatLargeNumber(7.891e6)).toBe('7.89M');
    });

    it('formats smaller numbers with commas', () => {
      expect(formatLargeNumber(12345)).toBe('12,345');
      expect(formatLargeNumber(999999)).toBe('999,999');
    });
  });

  describe('shortenAddress', () => {
    it('returns shortened address correctly', () => {
      const addr = '1234567890abcdef1234567890abcdef';
      expect(shortenAddress(addr)).toBe('1234567....0abcdef');
    });

    it('returns original string if shorter than 14 chars', () => {
      const addr = '1234567';
      expect(shortenAddress(addr)).toBe('1234567');
    });

    it('returns original string if exactly 14 chars', () => {
      const addr = '1234567890abcd';
      expect(shortenAddress(addr)).toBe('1234567890abcd');
    });

    it('returns "N/A" if input is undefined', () => {
      expect(shortenAddress(undefined as any)).toBe('N/A');
    });

    it('returns "N/A" if input is null', () => {
      expect(shortenAddress(null as any)).toBe('N/A');
    });

    it('returns "N/A" if input is empty string', () => {
      expect(shortenAddress('')).toBe('N/A');
    });
  });

  describe('getLatestTransactions', () => {
    it('fetches and returns data', async () => {
      const data = [{ id: 1 }, { id: 2 }];
      mockedAxios.get.mockResolvedValueOnce({ data });
      const result = await getLatestTransactions();
      expect(mockedAxios.get).toHaveBeenCalledWith(getMempoolRecentUrl());
      expect(result).toEqual(data);
    });

    it('throws error when request fails', async () => {
      mockedAxios.get.mockRejectedValueOnce(new Error('Network error'));
      await expect(getLatestTransactions()).rejects.toThrow('Network error');
    });
  });

  describe('getTxInfo', () => {
    it('fetches and returns tx info', async () => {
      const txid = 'abc123';
      const data = { txid, info: 'some info' };
      mockedAxios.get.mockResolvedValueOnce({ data });
      const result = await getTxInfo(txid);
      expect(mockedAxios.get).toHaveBeenCalledWith(
        getMempoolTransactionUrl(txid)
      );
      expect(result).toEqual(data);
    });

    it('throws error when request fails', async () => {
      mockedAxios.get.mockRejectedValueOnce(new Error('Request failed'));
      await expect(getTxInfo('txid')).rejects.toThrow('Request failed');
    });
  });
});
