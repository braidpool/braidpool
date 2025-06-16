import express from 'express';
import { rpcWithEnv } from '../utils/rpcWithEnv.js';
const router = express.Router();
const latencyHistory = [];
router.get('/', async (req, res) => {
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

    res.json({
      chartData: latencyHistory,
      averageLatency: latency.toFixed(2),
      peakLatency: peakLatency.toFixed(2),
      peerCount,
    });
  } catch (err) {
    console.error('[Latency] Error:', err.message);
    res.status(500).json({ error: 'Failed to fetch latency' });
  }
});

export default router;
