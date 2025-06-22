import { useEffect, useState, useCallback, useRef } from 'react';

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

// Global WebSocket instance and listeners
let globalWebSocket: WebSocket | null = null;
let globalListeners: Set<UseWebSocketOptions> = new Set();

const connect = () => {
  // Avoid creating multiple connections
  if (globalWebSocket && globalWebSocket.readyState !== WebSocket.CLOSED) {
    return;
  }

  globalWebSocket = new WebSocket('ws://localhost:5000');

  globalWebSocket.onopen = () => {
    globalListeners.forEach(l => l.onOpen?.());
  };

  globalWebSocket.onmessage = (event) => {
    try {
      const message = JSON.parse(event.data);
      globalListeners.forEach(l => l.onMessage?.(message));
    } catch (error) {
      console.error('[WebSocket] Failed to parse message:', error);
    }
  };

  globalWebSocket.onerror = (error) => {
    console.error('[WebSocket] Error:', error);
    globalListeners.forEach(l => l.onError?.(error));
  };

  globalWebSocket.onclose = () => {
    globalListeners.forEach(l => l.onClose?.());
    globalWebSocket = null; // Ensure we can reconnect
  };
};

export function useWebSocket(options: UseWebSocketOptions = {}) {
  const [isConnected, setIsConnected] = useState(
    globalWebSocket?.readyState === WebSocket.OPEN
  );
  
  // Use refs to store the latest callbacks to prevent effect re-runs
  const onMessageRef = useRef(options.onMessage);
  const onErrorRef = useRef(options.onError);
  const onOpenRef = useRef(options.onOpen);
  const onCloseRef = useRef(options.onClose);

  // Update refs when options change
  useEffect(() => {
    onMessageRef.current = options.onMessage;
    onErrorRef.current = options.onError;
    onOpenRef.current = options.onOpen;
    onCloseRef.current = options.onClose;
  });

  useEffect(() => {
    // Wrap callbacks to handle state updates within the hook
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

    // If already connected, manually trigger the onOpen to set initial state
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
    sendMessage
  };
} 