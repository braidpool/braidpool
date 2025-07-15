import { rpcWithEnv } from '../rpcWithEnv';
import { callRpc } from '../fetchRpc';

jest.mock('../fetchRpc', () => ({
  callRpc: jest.fn(),
}));

describe('rpcWithEnv', () => {
  beforeEach(() => {
    jest.clearAllMocks();

    // Simulate .env values
    process.env.BRAIDPOOL_URL = 'http://localhost:8332';
    process.env.RPC_USER = 'braiduser';
    process.env.RPC_PASS = 'braidpass';
  });

  it('calls callRpc with method and params', async () => {
    callRpc.mockResolvedValueOnce('success');

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

    expect(result).toBe('success');
  });

  it('defaults params to empty array if not provided', async () => {
    callRpc.mockResolvedValueOnce('defaultParams');

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

    expect(result).toBe('defaultParams');
  });

  it('propagates errors from callRpc', async () => {
    callRpc.mockRejectedValueOnce(new Error('RPC failed'));

    await expect(rpcWithEnv({ method: 'getblockchaininfo' })).rejects.toThrow(
      'RPC failed'
    );
  });
});
