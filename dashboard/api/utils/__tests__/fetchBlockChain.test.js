import { fetchAllNodeData } from '../fetchBlockChainInfo';
import {
  getBlockchainInfo,
  getPeerInfo,
  getMempoolInfo,
  getNetworkInfo,
  getNetTotals,
} from '../rpcMethods';

jest.mock('../rpcMethods', () => ({
  getBlockchainInfo: jest.fn(),
  getPeerInfo: jest.fn(),
  getMempoolInfo: jest.fn(),
  getNetworkInfo: jest.fn(),
  getNetTotals: jest.fn(),
}));

describe('fetchAllNodeData', () => {
  beforeEach(() => {
    jest.clearAllMocks();
    jest.spyOn(console, 'error').mockImplementation(() => {});

    // Mock Date to ensure consistent timestamps in tests
    jest
      .spyOn(Date.prototype, 'toISOString')
      .mockReturnValue('2024-01-15T10:30:00.000Z');
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should fetch all node data successfully', async () => {
    // Mock data for each RPC method
    const mockBlockchainInfo = {
      chain: 'main',
      blocks: 820000,
      difficulty: 62463471666532.41,
      verificationprogress: 0.999999,
    };

    const mockPeerInfo = [
      { id: 1, addr: '192.168.1.100:8333', version: 70016 },
      { id: 2, addr: '10.0.0.50:8333', version: 70016 },
    ];

    const mockNetworkInfo = {
      version: 250000,
      subversion: '/Satoshi:25.0.0/',
      protocolversion: 70016,
      connections: 8,
    };

    const mockMempoolInfo = {
      size: 2500,
      bytes: 15000000,
      usage: 32000000,
      maxmempool: 300000000,
    };

    const mockNetTotals = {
      totalbytesrecv: 125000000,
      totalbytessent: 98000000,
      timemillis: 1705317000000,
    };

    // Set up mocks
    getBlockchainInfo.mockResolvedValue(mockBlockchainInfo);
    getPeerInfo.mockResolvedValue(mockPeerInfo);
    getNetworkInfo.mockResolvedValue(mockNetworkInfo);
    getMempoolInfo.mockResolvedValue(mockMempoolInfo);
    getNetTotals.mockResolvedValue(mockNetTotals);

    const result = await fetchAllNodeData();

    // Verify all RPC methods were called
    expect(getBlockchainInfo).toHaveBeenCalledTimes(1);
    expect(getPeerInfo).toHaveBeenCalledTimes(1);
    expect(getNetworkInfo).toHaveBeenCalledTimes(1);
    expect(getMempoolInfo).toHaveBeenCalledTimes(1);
    expect(getNetTotals).toHaveBeenCalledTimes(1);

    // Verify the returned data structure
    expect(result).toEqual({
      type: 'node_health_data',
      data: {
        blockchainInfo: mockBlockchainInfo,
        peerInfo: mockPeerInfo,
        networkInfo: mockNetworkInfo,
        mempoolInfo: mockMempoolInfo,
        netTotals: mockNetTotals,
        lastUpdated: '2024-01-15T10:30:00.000Z',
      },
    });
  });

  it('should call all RPC methods concurrently using Promise.all', async () => {
    // Mock all methods to resolve after different delays to test concurrency
    getBlockchainInfo.mockImplementation(
      () =>
        new Promise((resolve) => setTimeout(() => resolve({ blocks: 1 }), 50))
    );
    getPeerInfo.mockImplementation(
      () => new Promise((resolve) => setTimeout(() => resolve([]), 30))
    );
    getNetworkInfo.mockImplementation(
      () =>
        new Promise((resolve) => setTimeout(() => resolve({ version: 1 }), 40))
    );
    getMempoolInfo.mockImplementation(
      () => new Promise((resolve) => setTimeout(() => resolve({ size: 0 }), 20))
    );
    getNetTotals.mockImplementation(
      () =>
        new Promise((resolve) =>
          setTimeout(() => resolve({ totalbytesrecv: 0 }), 10)
        )
    );

    const startTime = Date.now();
    await fetchAllNodeData();
    const endTime = Date.now();

    expect(endTime - startTime).toBeLessThan(100); // Allow some buffer for test execution

    // Verify all methods were called
    expect(getBlockchainInfo).toHaveBeenCalledTimes(1);
    expect(getPeerInfo).toHaveBeenCalledTimes(1);
    expect(getNetworkInfo).toHaveBeenCalledTimes(1);
    expect(getMempoolInfo).toHaveBeenCalledTimes(1);
    expect(getNetTotals).toHaveBeenCalledTimes(1);
  });

  it('should handle empty/null responses from RPC methods', async () => {
    // Test with various empty/null responses
    getBlockchainInfo.mockResolvedValue(null);
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue(undefined);
    getNetTotals.mockResolvedValue(null);

    const result = await fetchAllNodeData();

    expect(result).toEqual({
      type: 'node_health_data',
      data: {
        blockchainInfo: null,
        peerInfo: [],
        networkInfo: {},
        mempoolInfo: undefined,
        netTotals: null,
        lastUpdated: '2024-01-15T10:30:00.000Z',
      },
    });
  });

  it('should throw error when getBlockchainInfo fails', async () => {
    const blockchainError = new Error('Blockchain RPC failed');
    getBlockchainInfo.mockRejectedValue(blockchainError);
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockResolvedValue({});

    await expect(fetchAllNodeData()).rejects.toThrow('Blockchain RPC failed');

    expect(console.error).toHaveBeenCalledWith(
      'Failed to fetch all node data:',
      blockchainError
    );
  });

  it('should throw error when getPeerInfo fails', async () => {
    const peerError = new Error('Peer info unavailable');
    getBlockchainInfo.mockResolvedValue({});
    getPeerInfo.mockRejectedValue(peerError);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockResolvedValue({});

    await expect(fetchAllNodeData()).rejects.toThrow('Peer info unavailable');

    expect(console.error).toHaveBeenCalledWith(
      'Failed to fetch all node data:',
      peerError
    );
  });

  it('should throw error when getNetworkInfo fails', async () => {
    const networkError = new Error('Network info error');
    getBlockchainInfo.mockResolvedValue({});
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockRejectedValue(networkError);
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockResolvedValue({});

    await expect(fetchAllNodeData()).rejects.toThrow('Network info error');

    expect(console.error).toHaveBeenCalledWith(
      'Failed to fetch all node data:',
      networkError
    );
  });

  it('should throw error when getMempoolInfo fails', async () => {
    const mempoolError = new Error('Mempool data corrupt');
    getBlockchainInfo.mockResolvedValue({});
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockRejectedValue(mempoolError);
    getNetTotals.mockResolvedValue({});

    await expect(fetchAllNodeData()).rejects.toThrow('Mempool data corrupt');

    expect(console.error).toHaveBeenCalledWith(
      'Failed to fetch all node data:',
      mempoolError
    );
  });

  it('should throw error when getNetTotals fails', async () => {
    const netTotalsError = new Error('Network totals unavailable');
    getBlockchainInfo.mockResolvedValue({});
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockRejectedValue(netTotalsError);

    await expect(fetchAllNodeData()).rejects.toThrow(
      'Network totals unavailable'
    );

    expect(console.error).toHaveBeenCalledWith(
      'Failed to fetch all node data:',
      netTotalsError
    );
  });

  it('should throw error when multiple RPC methods fail', async () => {
    const error1 = new Error('Multiple failures');
    const error2 = new Error('Another failure');

    getBlockchainInfo.mockRejectedValue(error1);
    getPeerInfo.mockRejectedValue(error2);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockResolvedValue({});
    await expect(fetchAllNodeData()).rejects.toThrow('Multiple failures');

    expect(console.error).toHaveBeenCalledWith(
      'Failed to fetch all node data:',
      error1
    );
  });

  it('should generate current timestamp for lastUpdated', async () => {
    Date.prototype.toISOString.mockRestore();

    getBlockchainInfo.mockResolvedValue({});
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockResolvedValue({});

    const beforeTime = new Date().toISOString();
    const result = await fetchAllNodeData();
    const afterTime = new Date().toISOString();

    expect(result.data.lastUpdated).toMatch(
      /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{3}Z$/
    );
    expect(result.data.lastUpdated >= beforeTime).toBe(true);
    expect(result.data.lastUpdated <= afterTime).toBe(true);
  });

  it('should return correct data type', async () => {
    getBlockchainInfo.mockResolvedValue({});
    getPeerInfo.mockResolvedValue([]);
    getNetworkInfo.mockResolvedValue({});
    getMempoolInfo.mockResolvedValue({});
    getNetTotals.mockResolvedValue({});

    const result = await fetchAllNodeData();

    expect(result.type).toBe('node_health_data');
    expect(typeof result.data).toBe('object');
    expect(Array.isArray(result.data)).toBe(false);
    expect(result.data).toHaveProperty('blockchainInfo');
    expect(result.data).toHaveProperty('peerInfo');
    expect(result.data).toHaveProperty('networkInfo');
    expect(result.data).toHaveProperty('mempoolInfo');
    expect(result.data).toHaveProperty('netTotals');
    expect(result.data).toHaveProperty('lastUpdated');
  });
});
