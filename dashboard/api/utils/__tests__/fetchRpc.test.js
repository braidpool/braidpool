import axios from 'axios';
import { callRpc } from '../fetchRpc';

jest.mock('axios');

describe('callRpc', () => {
  const mockArgs = {
    url: 'http://localhost:8332',
    user: 'rpcuser',
    pass: 'rpcpass',
    method: 'getblockchaininfo',
    params: [],
  };

  beforeEach(() => {
    jest.clearAllMocks();
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should return result on success', async () => {
    axios.post.mockResolvedValueOnce({
      data: {
        result: { chain: 'main' },
        error: null,
      },
    });

    const result = await callRpc(mockArgs);

    expect(result).toEqual({ chain: 'main' });
    expect(axios.post).toHaveBeenCalledTimes(1);
  });

  it('should throw if response has an error field', async () => {
    axios.post.mockResolvedValueOnce({
      data: {
        result: null,
        error: { code: -32601, message: 'Method not found' },
      },
    });

    const expectedError = JSON.stringify({
      code: -32601,
      message: 'Method not found',
    });

    await expect(callRpc(mockArgs)).rejects.toThrow(expectedError);
  });

  it('should retry on failure and succeed eventually', async () => {
    axios.post
      .mockRejectedValueOnce(new Error('Temporary network error'))
      .mockResolvedValueOnce({
        data: { result: { synced: true }, error: null },
      });

    const result = await callRpc(mockArgs, 2, 10); // retries = 2, delay = 10ms

    expect(result).toEqual({ synced: true });
    expect(console.warn).toHaveBeenCalledWith(
      'RPC call failed (attempt 1): Retrying in 10ms...'
    );
    expect(axios.post).toHaveBeenCalledTimes(2);
  });

  it('should retry and fail after max retries', async () => {
    axios.post.mockRejectedValue(new Error('Server not responding'));

    await expect(callRpc(mockArgs, 2, 5)).rejects.toThrow(
      'Server not responding'
    );

    expect(console.error).toHaveBeenCalledWith(
      'RPC call failed after 2 attempts.'
    );
    expect(axios.post).toHaveBeenCalledTimes(2);
  });

  it('should respect custom timeout value', async () => {
    axios.post.mockResolvedValueOnce({
      data: { result: 'test', error: null },
    });

    await callRpc({ ...mockArgs }, 1, 10, 3000); // 1 retry, 10ms delay, 3s timeout

    expect(axios.post).toHaveBeenCalledWith(
      mockArgs.url,
      expect.anything(), // payload
      expect.objectContaining({
        timeout: 3000,
        auth: { username: 'rpcuser', password: 'rpcpass' },
        headers: { 'Content-Type': 'application/json' },
      })
    );
  });
});
