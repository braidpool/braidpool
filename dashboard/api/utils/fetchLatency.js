import { rpcWithEnv } from './rpcWithEnv.js';

export async function fetchLatencyData(wss) {
  try {
    const peers = await rpcWithEnv({
      method: 'getpeerinfo',
    });

    const now = Date.now();
    const totalPeers = peers.length;

    const validPings = peers
      .filter((peer) => typeof peer.pingtime === 'number' && peer.pingtime > 0)
      .map((peer) => Math.round(peer.pingtime * 1000))
      .filter((ping) => ping < 10000);

    if (validPings.length === 0) {
      console.warn('[LatencyStats] No valid pings to record.');
      const payload = {
        type: 'latency_data',
        data: {
          pings: [],
          averageLatency: 0,
          peakLatency: 0,
          peerCount: totalPeers,
          validPings: 0,
          timestamp: now,
        },
      };

      wss.clients.forEach((client) => {
        if (client.readyState === client.OPEN) {
          client.send(JSON.stringify(payload));
        }
      });
      return;
    }

    const averageLatency =
      validPings.reduce((a, b) => a + b, 0) / validPings.length;
    const peakLatency = Math.max(...validPings);

    const payload = {
      type: 'latency_data',
      data: {
        pings: validPings,
        averageLatency: averageLatency,
        peakLatency: peakLatency,
        peerCount: totalPeers,
        validPings: validPings.length,
        timestamp: now,
      },
    };
    console.log('Latency details', payload.data);

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error('[LatencyStats] Error:', err.message);
  }
}
