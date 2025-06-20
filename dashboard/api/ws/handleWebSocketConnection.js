import { callRpc } from '../utils/fetchRpc.js';

export async function handleWebSocketConnection(ws, wss) {
  console.log('Client connected');
  ws.send(JSON.stringify({ type: 'connection', status: 'connected' }));

  ws.on('message', async (message) => {
    try {
      const data = JSON.parse(message);

      if (data.type === 'rpc_call') {
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
}
