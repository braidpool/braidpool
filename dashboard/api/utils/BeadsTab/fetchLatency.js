import { rpcWithEnv } from './rpcWithEnv.js';

const latencyHistory = [];
export async function fetchLatencyData(wss) {
  try {
    const peers = await rpcWithEnv({
      method: 'getpeerinfo',
    });
    const pings = peers
      .map((peer) => peer.pingtime)
      .filter((t) => typeof t === 'number');

    const avgPing = pings.length
      ? pings.reduce((a, b) => a + b, 0) / pings.length
      : 0;
    const peakLatency = pings.length ? Math.max(...pings) * 1000 : 0;
    const peerCount = pings.length;
    const latency = Math.round(avgPing * 1000);
    const timestamp = new Date().toISOString();

    latencyHistory.push({
      value: latency,
      label: new Date(timestamp).toLocaleString(),
      date: timestamp,
    });

    if (latencyHistory.length > 100) latencyHistory.shift();

    const payload = {
      type: 'latency_update',
      data: {
        chartData: latencyHistory,
        averageLatency: latency.toFixed(2),
        peakLatency: peakLatency.toFixed(2),
        peerCount,
      },
    };
    console.log(' Broadcasting latency_update');

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error('[LatencyStats] Error:', err.message);
  }
}
