import { StrictMode } from 'react';
import { act, renderHook } from '@testing-library/react';
import { WEBSOCKET_URLS } from '../../URLs';
import { useNodeRpc } from '../useNodeRpc';

class MockSocket {
  static CONNECTING = 0;
  static OPEN = 1;
  static CLOSED = 3;
  static instances: MockSocket[] = [];

  readyState = MockSocket.CONNECTING;
  onopen: (() => void) | null = null;
  onclose: ((event: CloseEvent) => void) | null = null;
  onmessage: ((event: { data: string }) => void) | null = null;
  send = jest.fn<void, [string]>();
  close = jest.fn(() => {
    this.readyState = MockSocket.CLOSED;
    this.onclose?.(new CloseEvent('close'));
  });

  constructor(readonly url: string) {
    MockSocket.instances.push(this);
  }

  open() {
    this.readyState = MockSocket.OPEN;
    this.onopen?.();
  }

  receive(message: object) {
    this.onmessage?.({ data: JSON.stringify({ jsonrpc: '2.0', ...message }) });
  }
}

const originalWebSocket = globalThis.WebSocket;

beforeEach(() => {
  jest.useFakeTimers();
  globalThis.WebSocket = MockSocket as unknown as typeof WebSocket;
  MockSocket.instances = [];
});

afterEach(() => {
  jest.useRealTimers();
  globalThis.WebSocket = originalWebSocket;
});

function connect() {
  act(() => jest.advanceTimersByTime(0));
  const socket = MockSocket.instances[0];
  act(() => socket.open());
  return socket;
}

test('matches out-of-order replies and forwards subscription notifications', async () => {
  const onNotification = jest.fn();
  const { result } = renderHook(() => useNodeRpc({ onNotification }));
  const socket = connect();
  expect(socket.url).toBe(WEBSOCKET_URLS.NODE_RPC_WS);

  const info = result.current.rpc('getbraidinfo');
  const parents = result.current.rpc('getparents', ['hash']);
  expect(JSON.parse(socket.send.mock.calls[1][0])).toEqual({
    jsonrpc: '2.0',
    id: 2,
    method: 'getparents',
    params: ['hash'],
  });

  const failed = expect(parents).rejects.toThrow('unknown bead');
  socket.receive({ id: 2, error: { code: 1, message: 'unknown bead' } });
  socket.receive({
    method: 'subscribebead',
    params: { result: { hash: 'a' } },
  });
  socket.receive({ id: 1, result: { bead_count: 1 } });

  await failed;
  await expect(info).resolves.toEqual({ bead_count: 1 });
  expect(onNotification).toHaveBeenCalledWith('subscribebead', { hash: 'a' });
});

test('rejects pending calls and cancels the scheduled reconnect on unmount', async () => {
  const { result, unmount } = renderHook(() => useNodeRpc({}));
  const socket = connect();
  const pending = expect(result.current.rpc('getbraidinfo')).rejects.toThrow(
    'WebSocket closed'
  );

  act(() => socket.close());
  await pending;
  expect(result.current.connectionStatus).toBe('disconnected');

  unmount();
  act(() => jest.advanceTimersByTime(30_000));
  expect(MockSocket.instances).toHaveLength(1);
  expect(jest.getTimerCount()).toBe(0);
});

test('closes a socket that is still connecting when the component unmounts', () => {
  const { unmount } = renderHook(() => useNodeRpc({}));
  act(() => jest.advanceTimersByTime(0));
  const socket = MockSocket.instances[0];

  unmount();
  expect(socket.close).toHaveBeenCalledTimes(1);
  expect(jest.getTimerCount()).toBe(0);
});

test('creates one socket during effect replay and reconnects after a disconnect', async () => {
  const onOpen = jest.fn();
  const { result, unmount } = renderHook(() => useNodeRpc({ onOpen }), {
    wrapper: StrictMode,
  });
  await expect(result.current.rpc('getbraidinfo')).rejects.toThrow(
    'WebSocket is not connected'
  );
  const first = connect();
  expect(MockSocket.instances).toHaveLength(1);

  act(() => first.close());
  act(() => jest.advanceTimersByTime(1_000));
  const second = MockSocket.instances[1];
  act(() => second.open());
  expect(onOpen).toHaveBeenCalledTimes(2);
  expect(result.current.connectionStatus).toBe('connected');

  const timeout = expect(result.current.rpc('getbraidinfo')).rejects.toThrow(
    'RPC timeout: getbraidinfo'
  );
  act(() => jest.advanceTimersByTime(15_000));
  await timeout;

  const pending = expect(result.current.rpc('gettips')).rejects.toThrow(
    'WebSocket closed'
  );
  unmount();
  await pending;
  expect(second.close).toHaveBeenCalledTimes(1);
  expect(jest.getTimerCount()).toBe(0);
});
