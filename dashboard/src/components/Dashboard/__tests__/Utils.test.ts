import axios from 'axios';
import { getBlockInfo, fetchPreviousBlocks } from '../Utils';

jest.mock('axios');
const mockedAxios = axios as jest.Mocked<typeof axios>;

describe('Utility Functions', () => {
  describe('getBlockInfo', () => {
    it('fetches and returns block info', async () => {
      const hash = 'hash123#';
      const resp = { hash, info: 'random data' };
      mockedAxios.get.mockResolvedValueOnce({ data: resp });
      const result = await getBlockInfo(hash);

      expect(mockedAxios.get).toHaveBeenCalledWith(
        `http://localhost:8999/api/v1/block/${hash}`
      );
      expect(result).toEqual(resp);
    });

    it('throws error when request fails', async () => {
      mockedAxios.get.mockRejectedValueOnce(new Error('Request failed'));

      await expect(getBlockInfo('hash')).rejects.toThrow('Request failed');
    });
  });

  describe('fetchPreviousBlocks', () => {
    beforeEach(() => {
      global.fetch = jest.fn();
    });

    afterEach(() => {
      jest.resetAllMocks();
    });

    it('fetches and returns previous blocks', async () => {
      const data = [{ id: 1 }, { id: 2 }];
      (global.fetch as jest.Mock).mockResolvedValueOnce({
        ok: true,
        json: async () => data,
      });

      const result = await fetchPreviousBlocks();

      expect(global.fetch).toHaveBeenCalledWith(
        'http://localhost:8999/api/v1/blocks'
      );
      expect(result).toEqual(data);
    });

    it('throws error if response is not ok', async () => {
      (global.fetch as jest.Mock).mockResolvedValueOnce({
        ok: false,
      });

      await expect(fetchPreviousBlocks()).rejects.toThrow(
        'Network response was not ok'
      );
    });

    it('throws error if fetch fails', async () => {
      (global.fetch as jest.Mock).mockRejectedValueOnce(
        new Error('Fetch failed')
      );

      await expect(fetchPreviousBlocks()).rejects.toThrow('Fetch failed');
    });
  });
});
