import { useEffect, useState, useCallback, useRef } from 'react';
import {
  processHashrateData,
  processLatencyData,
  processBlockData,
  processRewardsData,
} from '../lib/utils/dataProcessor';

interface WebSocketMessage {
  type: string;
  data: any;
}

interface UseWebSocketOptions {
  onMessage?: (message: WebSocketMessage) => void;
  onError?: (error: Event) => void;
  onOpen?: () => void;
  onClose?: () => void;
}

let globalWebSocket: WebSocket | null = null;
let globalListeners: Set<UseWebSocketOptions> = new Set();

const connect = () => {
  if (globalWebSocket && globalWebSocket.readyState !== WebSocket.CLOSED) {
    return;
  }

  globalWebSocket = new WebSocket('ws://localhost:5000');

  globalWebSocket.onopen = () => {
    globalListeners.forEach((l) => l.onOpen?.());
  };

  globalWebSocket.onmessage = (event) => {
    try {
      const message = JSON.parse(event.data);

      // Process data based on message type
      let processedMessage = message;
      switch (message.type) {
        case 'hashrate_data':
          processedMessage = {
            type: 'hashrate_update',
            data: processHashrateData(message.data),
          };
          break;
        case 'latency_data':
          processedMessage = {
            type: 'latency_update',
            data: processLatencyData(message.data),
          };
          break;
        case 'block_data':
          processedMessage = {
            type: 'Block_summary',
            data: processBlockData(message.data),
          };
          break;
        case 'rewards_data':
          processedMessage = {
            type: 'Rewards_update',
            data: processRewardsData(message.data),
          };
          break;
        case 'transaction_stats':
          break;
        default:
          break;
      }

      globalListeners.forEach((l) => l.onMessage?.(processedMessage));
    } catch (error) {
      console.error('[WebSocket] Failed to parse message:', error);
    }
  };

  globalWebSocket.onerror = (error) => {
    console.error('[WebSocket] Error:', error);
    globalListeners.forEach((l) => l.onError?.(error));
  };

  globalWebSocket.onclose = () => {
    globalListeners.forEach((l) => l.onClose?.());
    globalWebSocket = null;
  };
};

export function useWebSocket(options: UseWebSocketOptions = {}) {
  const [isConnected, setIsConnected] = useState(
    globalWebSocket?.readyState === WebSocket.OPEN
  );

  const onMessageRef = useRef(options.onMessage);
  const onErrorRef = useRef(options.onError);
  const onOpenRef = useRef(options.onOpen);
  const onCloseRef = useRef(options.onClose);

  useEffect(() => {
    onMessageRef.current = options.onMessage;
    onErrorRef.current = options.onError;
    onOpenRef.current = options.onOpen;
    onCloseRef.current = options.onClose;
  });

  useEffect(() => {
    const listener: UseWebSocketOptions = {
      onMessage: (message) => onMessageRef.current?.(message),
      onOpen: () => {
        setIsConnected(true);
        onOpenRef.current?.();
      },
      onClose: () => {
        setIsConnected(false);
        onCloseRef.current?.();
      },
      onError: (error) => onErrorRef.current?.(error),
    };

    globalListeners.add(listener);
    connect();

    if (globalWebSocket?.readyState === WebSocket.OPEN) {
      listener.onOpen?.();
    }

    return () => {
      globalListeners.delete(listener);
      if (globalListeners.size === 0 && globalWebSocket) {
        globalWebSocket.close();
      }
    };
  }, []); // Empty dependency array to prevent re-runs

  const sendMessage = useCallback((message: any) => {
    if (globalWebSocket && globalWebSocket.readyState === WebSocket.OPEN) {
      globalWebSocket.send(JSON.stringify(message));
    }
  }, []);

  return {
    isConnected,
    sendMessage,
  };
}
