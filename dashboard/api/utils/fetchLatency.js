import { rpcWithEnv } from './rpcWithEnv.js';

const latencyHistory = [];

export async function fetchLatencyData(wss) {
  try {
    const peers = await rpcWithEnv({
      method: 'getpeerinfo',
    });
    const now = new Date();
    const pings = peers
      .map((peer) => peer.pingtime)
      .filter((t) => typeof t === 'number' && t > 0 && t * 1000 < 10000)
      .map((ping) => ({
        value: Math.round(ping * 1000), // convert to ms
        timeStamp: now.toISOString(),
        date: now.toISOString(),
      }));

    latencyHistory.push(...pings);

    while (latencyHistory.length > 100) latencyHistory.shift();

    const payload = {
      type: 'latency_update',
      data: {
        chartData: latencyHistory,
        timestamp: now.getTime(),
      },
    };

    console.log('Broadcasting raw latency_update');

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error('[LatencyStats] Error:', err.message);
  }
}
