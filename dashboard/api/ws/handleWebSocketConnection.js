import { callRpc } from '../utils/fetchRpc.js';
import {
  latestBlockPayload,
  latestStatsPayload,
} from '../utils/fetchBlockDetails.js';

const ALLOWED_RPC_METHODS = new Set([
  'getblock',
  'getblockhash',
  'getdifficulty',
  'getnetworkhashps',
  'getmempoolinfo',
  'getpeerinfo',
  'getblockchaininfo',
]);

export async function handleWebSocketConnection(ws) {
  console.log('Client connected');
  ws.send(JSON.stringify({ type: 'connection', status: 'connected' }));

  if (latestBlockPayload) {
    ws.send(JSON.stringify(latestBlockPayload));
  }
  if (latestStatsPayload) {
    ws.send(JSON.stringify(latestStatsPayload));
  }

  ws.on('message', async (message) => {
    try {
      const data = JSON.parse(message);

      if (data.type === 'rpc_call') {
        if (!data.method || typeof data.method !== 'string') {
          ws.send(
            JSON.stringify({ type: 'error', message: 'Invalid method format' })
          );
          return;
        }

        if (!ALLOWED_RPC_METHODS.has(data.method)) {
          console.warn(
            `[SECURITY] Blocked unauthorized RPC method: ${data.method}`
          );
          ws.send(
            JSON.stringify({
              type: 'error',
              message: `RPC method "${data.method}" not allowed.`,
            })
          );
          return;
        }

        const result = await callRpc({
          url: process.env.BRAIDPOOL_URL,
          user: process.env.RPC_USER,
          pass: process.env.RPC_PASS,
          method: data.method,
          params: data.params || [],
        });

        ws.send(JSON.stringify({ type: 'rpc_response', id: data.id, result }));
      }
    } catch (err) {
      console.error('WS error:', err);
      ws.send(
        JSON.stringify({ type: 'error', message: 'Invalid request format' })
      );
    }
  });

  ws.on('close', () => {
    console.log('Client disconnected');
  });
}
