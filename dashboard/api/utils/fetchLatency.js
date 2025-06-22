import { rpcWithEnv } from './rpcWithEnv.js';

const latencyHistory = [];

export async function fetchLatencyData(wss) {
  try {
    const peers = await rpcWithEnv({
      method: 'getpeerinfo',
    });
    
    const now = new Date();
    const totalPeers = peers.length;
    
    const validPings = peers
      .filter((peer) => typeof peer.pingtime === 'number' && peer.pingtime > 0)
      .map((peer) => Math.round(peer.pingtime * 1000)) 
      .filter((ping) => ping < 10000); 

    if (validPings.length === 0) {
      console.warn('[LatencyStats] No valid pings to record.');
      const payload = {
        type: 'latency_update',
        data: {
          chartData: latencyHistory,
          averageLatency: '0ms',
          peakLatency: '0ms',
          peerCount: totalPeers,
          totalPeers: totalPeers,
          validPings: 0,
          timestamp: now.getTime(),
        },
      };

      wss.clients.forEach((client) => {
        if (client.readyState === client.OPEN) {
          client.send(JSON.stringify(payload));
        }
      });
      return;
    }

    // Create data points for each valid ping
    const pings = validPings.map((ping) => ({
      value: ping,
      label: now.toLocaleTimeString(),
      date: now.toISOString(),
      timeStamp: now.toISOString(),
    }));

    latencyHistory.push(...pings);

    // Keep only last 100 data points
    while (latencyHistory.length > 100) {
      latencyHistory.shift();
    }

    const averageLatency = validPings.reduce((a, b) => a + b, 0) / validPings.length;
    const peakLatency = Math.max(...validPings);

    const payload = {
      type: 'latency_update',
      data: {
        chartData: latencyHistory,
        averageLatency: `${averageLatency.toFixed(0)}ms`,
        peakLatency: `${peakLatency}ms`,
        peerCount: totalPeers, // Show total peers, not just those with pings
        totalPeers: totalPeers,
        validPings: validPings.length,
        timestamp: now.getTime(),
      },
    };

    console.log(`[LatencyStats] Broadcasting latency update: ${validPings.length}/${totalPeers} peers with valid pings, avg: ${averageLatency.toFixed(0)}ms`);

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error('[LatencyStats] Error:', err.message);
  }
}
