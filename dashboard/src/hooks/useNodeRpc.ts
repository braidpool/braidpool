import { useCallback, useEffect, useRef, useState } from 'react';
import { WEBSOCKET_URLS } from '../URLs';

const RPC_TIMEOUT_MS = 15_000;
const INITIAL_RECONNECT_DELAY_MS = 1_000;
const MAX_RECONNECT_DELAY_MS = 30_000;

type ConnectionStatus = 'connecting' | 'connected' | 'disconnected' | 'error';

interface RpcCallbacks {
  onOpen?: () => void;
  onClose?: (event: CloseEvent) => void;
  onNotification?: (method: string, result: unknown) => void;
}

interface PendingRequest {
  resolve: (result: unknown) => void;
  reject: (error: Error) => void;
  timer: ReturnType<typeof setTimeout>;
}

export function useNodeRpc(callbacks: RpcCallbacks) {
  const [connectionStatus, setConnectionStatus] =
    useState<ConnectionStatus>('connecting');
  const socketRef = useRef<WebSocket | null>(null);
  const nextId = useRef(0);
  const pending = useRef(new Map<number, PendingRequest>());
  const callbacksRef = useRef(callbacks);

  useEffect(() => {
    callbacksRef.current = callbacks;
  }, [callbacks]);

  const isConnected = useCallback(
    () => socketRef.current?.readyState === WebSocket.OPEN,
    []
  );

  const rpc = useCallback((method: string, params: unknown[] = []) => {
    const socket = socketRef.current;
    if (socket?.readyState !== WebSocket.OPEN) {
      return Promise.reject(new Error('WebSocket is not connected'));
    }

    return new Promise<unknown>((resolve, reject) => {
      const id = ++nextId.current;
      const timer = setTimeout(() => {
        pending.current.delete(id);
        reject(new Error(`RPC timeout: ${method}`));
      }, RPC_TIMEOUT_MS);
      pending.current.set(id, { resolve, reject, timer });

      try {
        socket.send(JSON.stringify({ jsonrpc: '2.0', id, method, params }));
      } catch (error) {
        clearTimeout(timer);
        pending.current.delete(id);
        reject(error);
      }
    });
  }, []);

  useEffect(() => {
    const requests = pending.current;
    let reconnectDelay = INITIAL_RECONNECT_DELAY_MS;

    function rejectPending(message: string) {
      for (const { reject, timer } of requests.values()) {
        clearTimeout(timer);
        reject(new Error(message));
      }
      requests.clear();
    }

    function connect() {
      setConnectionStatus('connecting');
      const socket = new WebSocket(WEBSOCKET_URLS.NODE_RPC_WS);
      socketRef.current = socket;

      socket.onopen = () => {
        reconnectDelay = INITIAL_RECONNECT_DELAY_MS;
        setConnectionStatus('connected');
        callbacksRef.current.onOpen?.();
      };

      socket.onmessage = ({ data }: MessageEvent<string>) => {
        let message: unknown;
        try {
          message = JSON.parse(data);
        } catch {
          return;
        }

        if (typeof message !== 'object' || message === null) return;
        const { jsonrpc, id, error, result, method, params } = message as {
          jsonrpc?: unknown;
          id?: unknown;
          error?: unknown;
          result?: unknown;
          method?: unknown;
          params?: { result?: unknown };
        };
        if (jsonrpc !== '2.0') return;

        if (typeof id === 'number') {
          const request = requests.get(id);
          if (!request) return;
          clearTimeout(request.timer);
          requests.delete(id);
          if (error) request.reject(new Error(JSON.stringify(error)));
          else request.resolve(result);
        } else if (typeof method === 'string') {
          callbacksRef.current.onNotification?.(method, params?.result);
        }
      };

      socket.onerror = () => setConnectionStatus('error');
      socket.onclose = (event) => {
        socketRef.current = null;
        setConnectionStatus('disconnected');
        rejectPending('WebSocket closed');
        retry = setTimeout(connect, reconnectDelay);
        reconnectDelay = Math.min(reconnectDelay * 2, MAX_RECONNECT_DELAY_MS);
        callbacksRef.current.onClose?.(event);
      };
    }

    // Let React's development-only effect replay cancel the initial connection.
    let retry = setTimeout(connect, 0);
    return () => {
      clearTimeout(retry);
      const socket = socketRef.current;
      socketRef.current = null;
      if (socket) {
        socket.onmessage = null;
        socket.onerror = null;
        socket.onclose = null;
        socket.onopen = null;
        if (
          socket.readyState === WebSocket.CONNECTING ||
          socket.readyState === WebSocket.OPEN
        ) {
          socket.close();
        }
      }
      rejectPending('WebSocket closed');
    };
  }, []);

  return { rpc, isConnected, connectionStatus };
}
