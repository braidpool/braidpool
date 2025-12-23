import WebSocket from 'ws';
import { fetchBlockDetails } from '../fetchBlockDetails';
import { rpcWithEnv } from '../rpcWithEnv';

jest.mock('../rpcWithEnv', () => ({
  rpcWithEnv: jest.fn(),
}));

describe('fetchBlockDetails', () => {
  let mockWSS, mockClient;

  beforeEach(() => {
    WebSocket.CONNECTING = 0;
    WebSocket.OPEN = 1;
    WebSocket.CLOSING = 2;
    WebSocket.CLOSED = 3;

    mockClient = {
      readyState: WebSocket.OPEN,
      OPEN: WebSocket.OPEN,
      send: jest.fn(),
    };

    mockWSS = {
      clients: new Set([mockClient]),
    };

    rpcWithEnv.mockReset();

    jest.spyOn(console, 'error').mockImplementation(() => {});
    jest.spyOn(console, 'warn').mockImplementation(() => {});
    jest.spyOn(console, 'log').mockImplementation(() => {});
  });

  afterEach(() => {
    jest.restoreAllMocks();
  });

  it('should fetch and broadcast block + stats payloads', async () => {
    const fakeHash =
      '0000000000000000000a3e0b5f95b99b38f759ca9d6e13adcf937e2d4c9c8f5f';
    const coinbaseTxId =
      '4e9b5fdf2ac3b4e2e8f405c9e79d74f90f489c3d0b2b52ad5375192a12ec0e47';
    const txId =
      '1e0dc49a841f3ac919af7687ea8c273e7b06fbe7e61c3510dcfd1d3e7df8e0f1';
    const timestamp = 1720000000;

    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100 }) // getblockchaininfo
      .mockResolvedValueOnce(fakeHash) // getblockhash
      .mockResolvedValueOnce({
        hash: fakeHash,
        time: timestamp,
        tx: [
          { vout: [{ value: 6.25 }], txid: coinbaseTxId },
          { txid: txId, fee: 0.001, vsize: 200, vin: [{}], vout: [{}] },
        ],
        difficulty: 500000,
        previousblockhash:
          '0000000000000000000e1a8c5e0571b58c3d1ebd1f48e6c191e3c3195d68dcb9',
      }) // getblock
      .mockResolvedValueOnce({
        hash: fakeHash,
        time: timestamp,
        tx: [
          { vout: [{ value: 6.25 }], txid: coinbaseTxId },
          { txid: txId, fee: 0.001, vsize: 200, vin: [{}], vout: [{}] },
        ],
        difficulty: 500000,
        previousblockhash:
          '0000000000000000000e1a8c5e0571b58c3d1ebd1f48e6c191e3c3195d68dcb9',
      })
      .mockResolvedValueOnce({ size: 10 }); // getmempoolinfo

    await fetchBlockDetails(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(5);
    expect(mockClient.send).toHaveBeenCalledTimes(2);

    const blockMsg = JSON.parse(mockClient.send.mock.calls[0][0]);
    const statsMsg = JSON.parse(mockClient.send.mock.calls[1][0]);

    expect(blockMsg.type).toBe('block_data');
    expect(blockMsg.data.blockHash).toBe(fakeHash);
    expect(statsMsg.type).toBe('transaction_stats');
  });

  it('should not fetch again if block hash hasn’t changed', async () => {
    const hash =
      '000000000000000000051da0d0ae87f8e58b1e03e4e0872f9b1d80e4fa0a6cb1';
    const timestamp = 1720000000;

    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100 })
      .mockResolvedValueOnce(hash)
      .mockResolvedValueOnce({
        hash,
        time: timestamp,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'cb1coinbase' },
          { txid: 'cb1tx', fee: 0.001, vsize: 200, vin: [{}], vout: [{}] },
        ],
        difficulty: 500000,
        previousblockhash:
          '0000000000000000000d5e7d2d3c1b1a1e0f5c3d2e4f6b7a8c9d0e1f2a3b4c5d',
      })
      .mockResolvedValueOnce({
        hash,
        time: timestamp,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'cb1coinbase' },
          { txid: 'cb1tx', fee: 0.001, vsize: 200, vin: [{}], vout: [{}] },
        ],
        difficulty: 500000,
        previousblockhash:
          '0000000000000000000d5e7d2d3c1b1a1e0f5c3d2e4f6b7a8c9d0e1f2a3b4c5d',
      })
      .mockResolvedValueOnce({ size: 10 });

    await fetchBlockDetails(mockWSS);

    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 100 })
      .mockResolvedValueOnce(hash);

    await fetchBlockDetails(mockWSS);

    expect(rpcWithEnv).toHaveBeenCalledTimes(7);
    expect(mockClient.send).toHaveBeenCalledTimes(2);
  });

  it('should handle mempool RPC failure gracefully', async () => {
    const hash =
      '0000000000000000000abcdefabcdefabcdefabcdefabcdefabcdefabcdefab';
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 101 })
      .mockResolvedValueOnce(hash)
      .mockResolvedValueOnce({
        hash,
        time: 1720000200,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'cba' },
          { txid: 'tx1', fee: 0.002, vsize: 300, vin: [{}], vout: [{}] },
        ],
        difficulty: 700000,
        previousblockhash:
          '0000000000000000000f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f',
      })
      .mockResolvedValueOnce({
        hash,
        time: 1720000200,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'cba' },
          { txid: 'tx1', fee: 0.002, vsize: 300, vin: [{}], vout: [{}] },
        ],
        difficulty: 700000,
        previousblockhash:
          '0000000000000000000f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f',
      })
      .mockRejectedValueOnce(new Error('mempool down'));

    await fetchBlockDetails(mockWSS);

    expect(mockClient.send).toHaveBeenCalledTimes(2);
    const statsMsg = JSON.parse(mockClient.send.mock.calls[1][0]);
    expect(statsMsg.data.mempoolSize).toBe(-1);
  });

  it('should broadcast error when block fetch fails', async () => {
    rpcWithEnv.mockRejectedValueOnce(new Error('RPC crashed'));

    await fetchBlockDetails(mockWSS);

    expect(mockClient.send).toHaveBeenCalledTimes(1);
    const errorPayload = JSON.parse(mockClient.send.mock.calls[0][0]);
    expect(errorPayload.type).toBe('error');
    expect(errorPayload.data.message).toMatch(/Block data fetch failed/);
  });

  it('should handle tx with no fee or size info safely', async () => {
    const hash =
      '0000000000000000000deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadb';
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 102 })
      .mockResolvedValueOnce(hash)
      .mockResolvedValueOnce({
        hash,
        time: 1720000300,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'coinbase' },
          { txid: 'tx2', vin: [{}], vout: [{}] }, // missing fee/size
        ],
        difficulty: 80000,
        previousblockhash:
          '0000000000000000000aabbccddeeff00112233445566778899aabbccddeeff0',
      })
      .mockResolvedValueOnce({
        hash,
        time: 1720000300,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'coinbase' },
          { txid: 'tx2', vin: [{}], vout: [{}] }, // missing fee/size
        ],
        difficulty: 80000,
        previousblockhash:
          '0000000000000000000aabbccddeeff00112233445566778899aabbccddeeff0',
      }) // duplicate getblock call
      .mockResolvedValueOnce({ size: 20 });

    await fetchBlockDetails(mockWSS);

    expect(mockClient.send).toHaveBeenCalledTimes(2);
    const statsMsg = JSON.parse(mockClient.send.mock.calls[1][0]);
    expect(statsMsg.data.totalFees).toBe(0);
    expect(statsMsg.data.avgTxSize).toBe(0);
  });

  it('should not send when client is not OPEN', async () => {
    mockClient.readyState = WebSocket.CLOSING; // websocket closing
    rpcWithEnv
      .mockResolvedValueOnce({ blocks: 103 })
      .mockResolvedValueOnce('0000000000000000000notopen')
      .mockResolvedValueOnce({
        hash: '0000000000000000000notopen',
        time: 1720000400,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'coinbase' },
          { txid: 'tx3', fee: 0.001, vsize: 250, vin: [{}], vout: [{}] },
        ],
        difficulty: 90000,
        previousblockhash:
          '0000000000000000000ffeeddccbbaa99887766554433221100ffeeddccbbaa99',
      })
      .mockResolvedValueOnce({
        hash: '0000000000000000000notopen',
        time: 1720000400,
        tx: [
          { vout: [{ value: 6.25 }], txid: 'coinbase' },
          { txid: 'tx3', fee: 0.001, vsize: 250, vin: [{}], vout: [{}] },
        ],
        difficulty: 90000,
        previousblockhash:
          '0000000000000000000ffeeddccbbaa99887766554433221100ffeeddccbbaa99',
      })
      .mockResolvedValueOnce({ size: 30 });

    await fetchBlockDetails(mockWSS);

    expect(mockClient.send).not.toHaveBeenCalled();
  });
});
