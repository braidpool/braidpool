import WebSocket from 'ws';
import { fetchBlockDetails } from '../fetchBlockDetails';
import { rpcWithEnv } from '../rpcWithEnv';

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('fetchBlockDetails', () => {
  let mockWSS;
  let mockClient;
  let currentHash;
  let testCount = 0;

  const hash =
    '0000000000000000000a3e0b5f95b99b38f759ca9d6e13adcf937e2d4c9c8f5f';
  const block = {
    hash,
    time: 1720000000,
    tx: [
      { vout: [{ value: 6.25 }], txid: 'coinbase' },
      { txid: 'tx1', fee: 0.001, vsize: 200, vin: [{}], vout: [{}] },
    ],
    difficulty: 500000,
    previousblockhash:
      '0000000000000000000e1a8c5e0571b58c3d1ebd1f48e6c191e3c3195d68dcb9',
  };

  const mockNewBlock = (mempoolResult = { size: 10 }) => {
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100 })
      .mockResolvedValueOnce(currentHash)
      .mockResolvedValueOnce({ ...block, hash: currentHash })
      .mockResolvedValueOnce(mempoolResult);
  };

  beforeEach(() => {
    currentHash = `${hash}_${++testCount}`;
    mockClient = {
      readyState: WebSocket.OPEN,
      send: jest.fn(),
    };
    mockWSS = { clients: new Set([mockClient]) };
    rpcWithEnv.mockReset();

    jest.spyOn(console, 'error').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'log').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('fetches and broadcasts block and transaction stats', async () => {
    mockNewBlock();

    await fetchBlockDetails(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(4);
    expect(mockClient.send).toHaveBeenCalledTimes(2);

    const blockMessage = JSON.parse(mockClient.send.mock.calls[0][0]);
    const statsMessage = JSON.parse(mockClient.send.mock.calls[1][0]);
    expect(blockMessage).toMatchObject({
      type: 'block_data',
      data: {
        blockHash: currentHash,
        height: 100,
        txCount: 2,
        nonCoinbaseTxCount: 1,
        reward: 6.25,
        parent: block.previousblockhash,
      },
    });
    expect(statsMessage).toMatchObject({
      type: 'transaction_stats',
      data: {
        mempoolSize: 10,
        avgFeeRate: 0,
        avgTxSize: 0,
        averagingWindow: 1,
      },
    });
  });

  it('does not fetch or broadcast again when the block hash is unchanged', async () => {
    mockNewBlock();
    await fetchBlockDetails(mockWSS);

    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100 })
      .mockResolvedValueOnce(currentHash);
    await fetchBlockDetails(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(6);
    expect(mockClient.send).toHaveBeenCalledTimes(2);
  });

  it('uses -1 for mempool size when the mempool RPC fails', async () => {
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100 })
      .mockResolvedValueOnce(currentHash)
      .mockResolvedValueOnce({ ...block, hash: currentHash })
      .mockRejectedValueOnce(new Error('mempool down'));

    await fetchBlockDetails(mockWSS);

    const statsMessage = JSON.parse(mockClient.send.mock.calls[1][0]);
    expect(statsMessage.data.mempoolSize).toBe(-1);
  });

  it('broadcasts an error when a block RPC fails', async () => {
    rpcWithEnv.mockRejectedValueOnce(new Error('RPC crashed'));

    await fetchBlockDetails(mockWSS);

    expect(mockClient.send).toHaveBeenCalledTimes(1);
    const errorMessage = JSON.parse(mockClient.send.mock.calls[0][0]);
    expect(errorMessage.type).toBe('error');
    expect(errorMessage.data.message).toMatch(/Block data fetch failed/);
  });

  it('does not send messages to a client that is not open', async () => {
    mockClient.readyState = WebSocket.OPEN + 1;
    mockNewBlock();

    await fetchBlockDetails(mockWSS);

    expect(mockClient.send).not.toHaveBeenCalled();
  });
});
