import { useEffect, useState } from 'react';
import { WEBSOCKET_URLS } from '../../URLs';

const NETWORK_HASHRATE_POLL_MS = 30_000;
const NETWORK_HASHRATE_REQUEST_ID = 1;
const RECONNECT_DELAY_MS = 3_000;

// Network hashrate in H/s, with the time the node's answer arrived (ms since epoch).
export type NetworkHashrateSample = { hashrate: number; timestamp: number };

export function UseBitcoinNetworkHashrate(): NetworkHashrateSample | null {
  const [sample, setSample] = useState<NetworkHashrateSample | null>(null);

  useEffect(() => {
    let cancelled = false;
    let ws: WebSocket | null = null;
    let reconnectTimer: ReturnType<typeof setTimeout> | undefined;

    const requestHashrate = () => {
      if (ws?.readyState !== WebSocket.OPEN) return;
      ws.send(
        JSON.stringify({
          jsonrpc: '2.0',
          id: NETWORK_HASHRATE_REQUEST_ID,
          method: 'bitcoinproxy',
          params: ['getnetworkhashps', []],
        })
      );
    };

    const connect = () => {
      if (cancelled) return;
      ws = new WebSocket(WEBSOCKET_URLS.NODE_RPC_WS);

      ws.onopen = requestHashrate;

      ws.onmessage = (event) => {
        if (cancelled) return;
        try {
          const message = JSON.parse(event.data as string);
          if (
            message.id === NETWORK_HASHRATE_REQUEST_ID &&
            typeof message.result === 'number'
          ) {
            setSample({ hashrate: message.result, timestamp: Date.now() });
          } else if (
            message.id === NETWORK_HASHRATE_REQUEST_ID &&
            message.error
          ) {
            console.warn('Network hashrate RPC error:', message.error.message);
          }
        } catch (err) {
          console.warn('Network hashrate parse error:', err);
        }
      };

      ws.onclose = () => {
        if (!cancelled) {
          setSample(null);
          reconnectTimer = setTimeout(connect, RECONNECT_DELAY_MS);
        }
      };
    };

    connect();
    const pollTimer = setInterval(requestHashrate, NETWORK_HASHRATE_POLL_MS);

    return () => {
      cancelled = true;
      clearInterval(pollTimer);
      clearTimeout(reconnectTimer);
      ws?.close();
    };
  }, []);

  return sample;
}
