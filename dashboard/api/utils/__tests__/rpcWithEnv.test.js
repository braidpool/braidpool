import { rpcWithEnv } from '../rpcWithEnv';
import { callRpc } from '../fetchRpc';

jest.mock('../fetchRpc', () => ({
  callRpc: jest.fn(),
}));

describe('rpcWithEnv', () => {
  const originalEnv = process.env;

  beforeEach(() => {
    jest.clearAllMocks();
    // Reset environment variables
    process.env = { ...originalEnv };

    // Set up default valid environment variables
    process.env.BRAIDPOOL_URL = 'http://localhost:8332';
    process.env.RPC_USER = 'braiduser';
    process.env.RPC_PASS = 'braidpass';
  });

  afterAll(() => {
    process.env = originalEnv;
  });

  describe('successful RPC calls', () => {
    it('calls callRpc with method and params', async () => {
      const mockResponse = { result: 'success' };
      callRpc.mockResolvedValueOnce(mockResponse);

      const result = await rpcWithEnv({
        method: 'getblock',
        params: ['000000000000000000', 1],
      });

      expect(callRpc).toHaveBeenCalledWith({
        url: 'http://localhost:8332',
        user: 'braiduser',
        pass: 'braidpass',
        method: 'getblock',
        params: ['000000000000000000', 1],
      });

      expect(result).toBe(mockResponse);
    });

    it('defaults params to empty array if not provided', async () => {
      const mockResponse = {
        chainwork:
          '000000000000000000000000000000000000000007616e2e2fdc5aa9153',
      };
      callRpc.mockResolvedValueOnce(mockResponse);

      const result = await rpcWithEnv({
        method: 'getblockchaininfo',
      });

      expect(callRpc).toHaveBeenCalledWith({
        url: 'http://localhost:8332',
        user: 'braiduser',
        pass: 'braidpass',
        method: 'getblockchaininfo',
        params: [],
      });

      expect(result).toBe(mockResponse);
    });

    it('handles empty params array explicitly', async () => {
      const mockResponse = { connections: 8 };
      callRpc.mockResolvedValueOnce(mockResponse);

      const result = await rpcWithEnv({
        method: 'getnetworkinfo',
        params: [],
      });

      expect(callRpc).toHaveBeenCalledWith({
        url: 'http://localhost:8332',
        user: 'braiduser',
        pass: 'braidpass',
        method: 'getnetworkinfo',
        params: [],
      });

      expect(result).toBe(mockResponse);
    });
  });

  describe('environment variable validation', () => {
    it('throws error when BRAIDPOOL_URL is missing', () => {
      delete process.env.BRAIDPOOL_URL;

      expect(() => rpcWithEnv({ method: 'getblockchaininfo' })).toThrow(
        'Missing BRAIDPOOL_URL, RPC_USER, or RPC_PASS'
      );

      expect(callRpc).not.toHaveBeenCalled();
    });

    it('throws error when RPC_USER is missing', () => {
      delete process.env.RPC_USER;

      expect(() => rpcWithEnv({ method: 'getblockchaininfo' })).toThrow(
        'Missing BRAIDPOOL_URL, RPC_USER, or RPC_PASS'
      );

      expect(callRpc).not.toHaveBeenCalled();
    });

    it('throws error when RPC_PASS is missing', () => {
      delete process.env.RPC_PASS;

      expect(() => rpcWithEnv({ method: 'getblockchaininfo' })).toThrow(
        'Missing BRAIDPOOL_URL, RPC_USER, or RPC_PASS'
      );

      expect(callRpc).not.toHaveBeenCalled();
    });

    it('throws error when BRAIDPOOL_URL is empty string', () => {
      process.env.BRAIDPOOL_URL = '';

      expect(() => rpcWithEnv({ method: 'getblockchaininfo' })).toThrow(
        'Missing BRAIDPOOL_URL, RPC_USER, or RPC_PASS'
      );

      expect(callRpc).not.toHaveBeenCalled();
    });

    it('throws error when multiple env vars are missing', () => {
      delete process.env.BRAIDPOOL_URL;
      delete process.env.RPC_USER;

      expect(() => rpcWithEnv({ method: 'getblockchaininfo' })).toThrow(
        'Missing BRAIDPOOL_URL, RPC_USER, or RPC_PASS'
      );

      expect(callRpc).not.toHaveBeenCalled();
    });
  });

  describe('error handling', () => {
    it('propagates errors from callRpc', async () => {
      const rpcError = new Error('Connection refused');
      callRpc.mockRejectedValueOnce(rpcError);

      await expect(rpcWithEnv({ method: 'getblockchaininfo' })).rejects.toThrow(
        'Connection refused'
      );

      expect(callRpc).toHaveBeenCalledWith({
        url: 'http://localhost:8332',
        user: 'braiduser',
        pass: 'braidpass',
        method: 'getblockchaininfo',
        params: [],
      });
    });

    it('propagates RPC-specific errors', async () => {
      const rpcError = new Error('Method not found');
      callRpc.mockRejectedValueOnce(rpcError);

      await expect(
        rpcWithEnv({
          method: 'invalidmethod',
          params: ['test'],
        })
      ).rejects.toThrow('Method not found');

      expect(callRpc).toHaveBeenCalledWith({
        url: 'http://localhost:8332',
        user: 'braiduser',
        pass: 'braidpass',
        method: 'invalidmethod',
        params: ['test'],
      });
    });
  });

  describe('console logging', () => {
    let consoleSpy;

    beforeEach(() => {
      consoleSpy = jest.spyOn(console, 'error').mockImplementation(() => {});
    });

    afterEach(() => {
      consoleSpy.mockRestore();
    });

    it('logs error when environment variables are missing', () => {
      delete process.env.BRAIDPOOL_URL;

      expect(() => rpcWithEnv({ method: 'getblockchaininfo' })).toThrow();

      expect(consoleSpy).toHaveBeenCalledWith(
        'Missing required RPC environment variables'
      );
    });

    it('logs error when callRpc fails', async () => {
      const rpcError = new Error('Network timeout');
      callRpc.mockImplementation(() => {
        throw rpcError;
      });

      try {
        await rpcWithEnv({ method: 'getblockchaininfo' });
      } catch (error) {
        // Expected to throw
      }

      expect(consoleSpy).toHaveBeenCalledWith(
        'RPC call failed: getblockchaininfo',
        rpcError
      );
    });
  });

  describe('different parameter types', () => {
    it('handles string parameters', async () => {
      const mockResponse = { hash: 'blockhash' };
      callRpc.mockResolvedValueOnce(mockResponse);

      await rpcWithEnv({
        method: 'getblock',
        params: ['000000000000000000'],
      });

      expect(callRpc).toHaveBeenCalledWith(
        expect.objectContaining({
          params: ['000000000000000000'],
        })
      );
    });

    it('handles mixed parameter types', async () => {
      const mockResponse = { txid: 'transaction' };
      callRpc.mockResolvedValueOnce(mockResponse);

      await rpcWithEnv({
        method: 'getrawtransaction',
        params: ['txhash', true, 'blockhash'],
      });

      expect(callRpc).toHaveBeenCalledWith(
        expect.objectContaining({
          params: ['txhash', true, 'blockhash'],
        })
      );
    });

    it('handles numeric parameters', async () => {
      const mockResponse = { height: 123456 };
      callRpc.mockResolvedValueOnce(mockResponse);

      await rpcWithEnv({
        method: 'getblockhash',
        params: [123456],
      });

      expect(callRpc).toHaveBeenCalledWith(
        expect.objectContaining({
          params: [123456],
        })
      );
    });
  });
});
