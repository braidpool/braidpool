import express from 'express';
import { rpcWithEnv } from '../utils/rpcWithEnv.js';
const router = express.Router();
const statsHistory = [];

router.get('/', async (req, res) => {
  const startTime = Date.now();
  try {
    const [hashrate, difficulty] = await Promise.all([
      rpcWithEnv({ method: 'getnetworkhashps' }),
      rpcWithEnv({ method: 'getdifficulty' }),
    ]);
    const latency = Date.now() - startTime;
    const timestamp = new Date().toISOString();
    const hashrateEH = hashrate / 1e18;
    const hashrateMH = hashrate / 1e6;
    statsHistory.push({
      value: hashrate,
      label: new Date(timestamp).toLocaleString(),
      date: timestamp,
      latency,
    });

    if (statsHistory.length > 100) statsHistory.shift();

    const values = statsHistory.map((entry) => entry.value);
    const avgHashrate = values.reduce((a, b) => a + b, 0) / values.length;
    const peakHashrate = Math.max(...values);

    res.json({
      chartData: statsHistory,
      averageHashrate: avgHashrate / 1e18,
      peakHashrate: peakHashrate / 1e18,
      networkDifficulty: difficulty,
      hashrateRaw: hashrate,
      hashrateEH: hashrateEH.toFixed(4),
      hashrateMH: hashrateMH.toFixed(2),
    });
  } catch (err) {
    console.error('[Stats] Error fetching stats:', err.message);
    res.status(500).json({ error: 'Failed to fetch stats' });
  }
});

export default router;
