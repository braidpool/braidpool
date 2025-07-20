import { handleWebSocketConnection } from '../handleWebSocketConnection';
import { callRpc } from '../../utils/fetchRpc';

jest.mock('../../utils/fetchRpc', () => ({
  callRpc: jest.fn(),
}));

jest.mock('../../utils/fetchBlockDetails', () => ({
  latestBlockPayload: { type: 'latest_block', data: { height: 123 } },
  latestStatsPayload: { type: 'latest_stats', data: { networkHash: 9999 } },
}));

describe('handleWebSocketConnection', () => {
  let mockWs;

  beforeEach(() => {
    mockWs = {
      send: jest.fn(),
      on: jest.fn((event, cb) => {
        if (event === 'message') mockWs._triggerMessage = cb;
        if (event === 'close') mockWs._triggerClose = cb;
      }),
    };

    jest.clearAllMocks();
  });

  test('sends connection confirmation and both payloads', () => {
    handleWebSocketConnection(mockWs);

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'connection', status: 'connected' })
    );
    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'latest_block', data: { height: 123 } })
    );
    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'latest_stats', data: { networkHash: 9999 } })
    );
  });

  test('handles valid rpc_call correctly', async () => {
    callRpc.mockResolvedValue({ dummy: 'data' });

    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(
      JSON.stringify({
        type: 'rpc_call',
        id: 'msg-1',
        method: 'getblock',
        params: ['blockHash'],
      })
    );

    expect(callRpc).toHaveBeenCalledWith({
      url: undefined,
      user: undefined,
      pass: undefined,
      method: 'getblock',
      params: ['blockHash'],
    });

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({
        type: 'rpc_response',
        id: 'msg-1',
        result: { dummy: 'data' },
      })
    );
  });

  test('rejects rpc_call with missing method', async () => {
    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(JSON.stringify({ type: 'rpc_call' }));

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'error', message: 'Invalid method format' })
    );
  });

  test('rejects rpc_call with non-string method', async () => {
    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(
      JSON.stringify({ type: 'rpc_call', method: 123 })
    );

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'error', message: 'Invalid method format' })
    );
  });

  test('rejects rpc_call with disallowed method', async () => {
    const originalWarn = console.warn;
    console.warn = jest.fn(); // Silence expected security log

    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(
      JSON.stringify({ type: 'rpc_call', method: 'shutdown' })
    );

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({
        type: 'error',
        message: 'RPC method "shutdown" not allowed.',
      })
    );

    console.warn = originalWarn;
  });

  test('returns error when message is invalid JSON', async () => {
    const originalError = console.error;
    console.error = jest.fn(); // Silence expected JSON parse error

    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage('{ not-json }');

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'error', message: 'Invalid request format' })
    );

    console.error = originalError;
  });

  test('handles unexpected internal error gracefully', async () => {
    const originalError = console.error;
    console.error = jest.fn(); // Silence expected internal error log

    callRpc.mockImplementation(() => {
      throw new Error('RPC failed');
    });

    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(
      JSON.stringify({
        type: 'rpc_call',
        id: 'msg-error',
        method: 'getblock',
      })
    );

    expect(mockWs.send).toHaveBeenCalledWith(
      JSON.stringify({ type: 'error', message: 'Invalid request format' })
    );

    console.error = originalError;
  });

  test('ignores unknown message types gracefully', async () => {
    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(
      JSON.stringify({ type: 'something_else', foo: 'bar' })
    );

    expect(mockWs.send).toHaveBeenCalledTimes(3); // connection + 2 payloads
  });

  test('logs on close', () => {
    console.log = jest.fn();

    handleWebSocketConnection(mockWs);
    mockWs._triggerClose();

    expect(console.log).toHaveBeenCalledWith('Client disconnected');
  });

  test('warns on disallowed method', async () => {
    console.warn = jest.fn();

    handleWebSocketConnection(mockWs);

    await mockWs._triggerMessage(
      JSON.stringify({ type: 'rpc_call', method: 'deleteall' })
    );

    expect(console.warn).toHaveBeenCalledWith(
      '[SECURITY] Blocked unauthorized RPC method: deleteall'
    );
  });
});
