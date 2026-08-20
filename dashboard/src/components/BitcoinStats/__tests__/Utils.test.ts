import axios from 'axios';
import {
  getCurrencySymbol,
  formatPrice,
  formatLargeNumber,
  shortenAddress,
  getLatestTransactions,
  getTxInfo,
} from '../Utils';

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
    beforeEach(() => {
      mockedAxios.post.mockReset();
    });

    it('fetches and returns transactions from node RPCs', async () => {
      // getmempoolentries
      mockedAxios.post.mockResolvedValueOnce({
        data: { result: [{ txid: 'aaaa', fee: 1000, vsize: 200, fee_rate: 5.0, time: 1000, rbf: false }], error: null },
      });
      // stagedtransactions
      mockedAxios.post.mockResolvedValueOnce({
        data: { result: [], error: null },
      });
      // getcommittedtransactions
      mockedAxios.post.mockResolvedValueOnce({
        data: { result: { transactions: [] }, error: null },
      });

      const result = await getLatestTransactions();
      expect(mockedAxios.post).toHaveBeenCalledTimes(3);
      expect(Array.isArray(result)).toBe(true);
      expect(result[0].txid).toBe('aaaa');
      expect(result[0].stage).toBe('mempool');
    });

    it('throws when all three RPC calls fail', async () => {
      mockedAxios.post.mockRejectedValue(new Error('Network error'));
      await expect(getLatestTransactions()).rejects.toThrow(
        'Unable to fetch transactions: node unreachable or all RPCs failed'
      );
    });
  });

  describe('getTxInfo', () => {
    beforeEach(() => {
      mockedAxios.post.mockReset();
    });

    it('fetches and returns tx info via gettransactionstatus', async () => {
      const txid = 'abc123';
      mockedAxios.post.mockResolvedValueOnce({
        data: {
          result: {
            txid,
            stage: 1,
            stage_name: 'mempool',
            detail: { fee: -0.0001, vsize: 200, size: 220, weight: 800, version: 2, locktime: 0, vin: [], vout: [] },
          },
          error: null,
        },
      });

      const result = await getTxInfo(txid);
      expect(mockedAxios.post).toHaveBeenCalledWith(
        expect.any(String),
        expect.objectContaining({ method: 'gettransactionstatus', params: [txid] }),
        expect.any(Object)
      );
      expect(result.txid).toBe(txid);
      expect(result.stage).toBe('mempool');
      expect(result.fee).toBe(10000); // 0.0001 BTC in sats
    });

    it('throws when the RPC returns an error', async () => {
      mockedAxios.post.mockResolvedValueOnce({
        data: { result: null, error: { message: 'Invalid txid' } },
      });
      await expect(getTxInfo('bad')).rejects.toThrow('Invalid txid');
    });

    it('throws when the network request fails', async () => {
      mockedAxios.post.mockRejectedValueOnce(new Error('Request failed'));
      await expect(getTxInfo('txid')).rejects.toThrow('Request failed');
    });
  });
});
