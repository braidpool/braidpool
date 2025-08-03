import axios from 'axios';
import { callRpc } from '../fetchRpc';

jest.mock('axios', () => ({
  post: jest.fn(),
}));

describe('callRpc', () => {
  const mockAxios = axios;
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
    mockAxios.post.mockResolvedValueOnce({
      data: {
        result: { chain: 'main' },
        error: null,
      },
    });

    const result = await callRpc(mockArgs);

    expect(result).toEqual({ chain: 'main' });
    expect(mockAxios.post).toHaveBeenCalledTimes(1);
  });

  it('should throw if response has an error field', async () => {
    const mockResponse = {
      data: {
        result: null,
        error: { code: -32601, message: 'Method not found' },
      },
      status: 200,
      statusText: 'OK',
      headers: {},
      config: {},
    };
    mockAxios.post.mockImplementation((url, payload, config) => {
      return Promise.resolve(mockResponse);
    });

    const expectedError = JSON.stringify({
      code: -32601,
      message: 'Method not found',
    });

    try {
      await callRpc(mockArgs);
      throw new Error('Expected callRpc to throw, but it did not');
    } catch (error) {
      console.log('Caught error:', error.message);
      expect(error.message).toBe(expectedError);
    }
  });

  it('should retry on failure and succeed eventually', async () => {
    mockAxios.post
      .mockRejectedValueOnce(new Error('Temporary network error'))
      .mockResolvedValueOnce({
        data: { result: { synced: true }, error: null },
      });

    const result = await callRpc(mockArgs, 2, 10); // retries = 2, delay = 10ms

    expect(result).toEqual({ synced: true });
    expect(console.warn).toHaveBeenCalledWith(
      'RPC call failed (attempt 1): Retrying in 10ms...'
    );
    expect(mockAxios.post).toHaveBeenCalledTimes(2);
  });

  it('should retry and fail after max retries', async () => {
    mockAxios.post.mockRejectedValue(new Error('Server not responding'));

    await expect(callRpc(mockArgs, 2, 5)).rejects.toThrow(
      'Server not responding'
    );

    expect(console.error).toHaveBeenCalledWith(
      'RPC call failed after 2 attempts.'
    );
    expect(mockAxios.post).toHaveBeenCalledTimes(2);
  });

  it('should respect custom timeout value', async () => {
    mockAxios.post.mockResolvedValueOnce({
      data: { result: 'test', error: null },
    });

    await callRpc({ ...mockArgs }, 1, 10, 3000); // 1 retry, 10ms delay, 3s timeout

    expect(mockAxios.post).toHaveBeenCalledWith(
      mockArgs.url,
      expect.anything(), // payload
      expect.objectContaining({
        timeout: 3000,
        auth: { username: 'rpcuser', password: 'rpcpass' },
        headers: { 'Content-Type': 'application/json' },
      })
    );
  });

  it('should handle axios error with no response data', async () => {
    // Test case where axios fails but doesn't have response.data
    const axiosError = new Error('Network Error');
    axiosError.response = undefined; // No response object

    mockAxios.post.mockRejectedValueOnce(axiosError);

    await expect(callRpc(mockArgs, 1)).rejects.toThrow('Network Error');
    expect(console.error).toHaveBeenCalledWith(
      'RPC call failed after 1 attempts.'
    );
  });

  it('should handle axios error with empty response', async () => {
    // Test case where axios returns a response but without data
    const axiosError = new Error('Request failed');
    axiosError.response = {}; // Empty response object

    mockAxios.post.mockRejectedValueOnce(axiosError);

    await expect(callRpc(mockArgs, 1)).rejects.toThrow('Request failed');
  });
});
