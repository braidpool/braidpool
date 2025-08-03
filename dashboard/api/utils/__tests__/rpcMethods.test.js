import {
  getBlockchainInfo,
  getPeerInfo,
  getNetworkInfo,
  getMempoolInfo,
  getNetTotals,
} from '../rpcMethods';
import { rpcWithEnv } from '../rpcWithEnv';

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('Blockchain Functions', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('getBlockchainInfo', () => {
    it('calls rpcWithEnv with correct method', async () => {
      rpcWithEnv.mockResolvedValueOnce({ blocks: 123456 });

      const result = await getBlockchainInfo();

      expect(rpcWithEnv).toHaveBeenCalledWith({ method: 'getblockchaininfo' });
      expect(result).toEqual({ blocks: 123456 });
    });

    it('propagates errors', async () => {
      const error = new Error('RPC failed');
      rpcWithEnv.mockRejectedValueOnce(error);

      await expect(getBlockchainInfo()).rejects.toThrow('RPC failed');
    });
  });

  describe('getPeerInfo', () => {
    it('calls rpcWithEnv with correct method', async () => {
      rpcWithEnv.mockResolvedValueOnce([{ id: 1 }]);

      const result = await getPeerInfo();

      expect(rpcWithEnv).toHaveBeenCalledWith({ method: 'getpeerinfo' });
      expect(result).toEqual([{ id: 1 }]);
    });
    it('propagates errors', async () => {
      const error = new Error('RPC error');
      rpcWithEnv.mockRejectedValueOnce(error);

      await expect(getPeerInfo()).rejects.toThrow('RPC error');
    });
  });

  describe('getNetworkInfo', () => {
    it('calls rpcWithEnv with correct method', async () => {
      rpcWithEnv.mockResolvedValueOnce({ version: 220000 });

      const result = await getNetworkInfo();

      expect(rpcWithEnv).toHaveBeenCalledWith({ method: 'getnetworkinfo' });
      expect(result).toEqual({ version: 220000 });
    });
    it('propagates errors', async () => {
      const error = new Error('RPC error');
      rpcWithEnv.mockRejectedValueOnce(error);

      await expect(getNetworkInfo()).rejects.toThrow('RPC error');
    });
  });

  describe('getMempoolInfo', () => {
    it('calls rpcWithEnv with correct method', async () => {
      rpcWithEnv.mockResolvedValueOnce({ size: 10 });

      const result = await getMempoolInfo();

      expect(rpcWithEnv).toHaveBeenCalledWith({ method: 'getmempoolinfo' });
      expect(result).toEqual({ size: 10 });
    });
    it('propagates errors', async () => {
      const error = new Error('RPC error');
      rpcWithEnv.mockRejectedValueOnce(error);

      await expect(getMempoolInfo()).rejects.toThrow('RPC error');
    });
  });

  describe('getNetTotals', () => {
    it('calls rpcWithEnv with correct method', async () => {
      rpcWithEnv.mockResolvedValueOnce({ totalbytesrecv: 1000 });

      const result = await getNetTotals();

      expect(rpcWithEnv).toHaveBeenCalledWith({ method: 'getnettotals' });
      expect(result).toEqual({ totalbytesrecv: 1000 });
    });
    it('propagates errors', async () => {
      const error = new Error('RPC error');
      rpcWithEnv.mockRejectedValueOnce(error);

      await expect(getNetTotals()).rejects.toThrow('RPC error');
    });
  });
});
