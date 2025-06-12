import 'dotenv/config';
import express from 'express';
import axios from 'axios';
import cors from 'cors';
const app = express();
const PORT = process.env.PORT || 3001;

const BRAIDPOOL_URL = process.env.BRAIDPOOL_URL;
const RPC_USER = process.env.RPC_USER;
const RPC_PASS = process.env.RPC_PASS;

const statsHistory = [];
const latencyHistory = [];

app.use(cors({ origin: 'http://localhost:3000', credentials: true }));
app.use(express.json());

async function callRpc(method, params = []) {
  try {
    const response = await axios.post(
      BRAIDPOOL_URL,
      {
        jsonrpc: '1.0',
        id: 'rpc-call',
        method,
        params,
      },
      {
        auth: { username: RPC_USER, password: RPC_PASS },
        headers: { 'Content-Type': 'text/plain' },
      }
    );
    return response.data.result;
  } catch (err) {
    console.error(
      `[callRpc] Error calling ${method}:`,
      err?.response?.data || err.message
    );
    throw err;
  }
}

// Generic RPC proxy
app.use('/api/node/:endpoint', async (req, res) => {
  try {
    const { endpoint } = req.params;
    console.log(`[Proxy] Request for endpoint: ${endpoint}`);
    const result = await callRpc(endpoint);
    res.json(result);
  } catch (error) {
    res.status(500).json({ error: 'Internal server error' });
  }
});

// Get transactions from a block
app.get('/api/beads/:blockHash/transactions', async (req, res) => {
  try {
    const block = await callRpc('getblock', [req.params.blockHash, 2]);
    res.json(block.tx);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// Network stats: hashrate, difficulty, latency
app.get('/api/stats', async (req, res) => {
  const startTime = Date.now();
  try {
    const [hashrate, difficulty] = await Promise.all([
      callRpc('getnetworkhashps'),
      callRpc('getdifficulty'),
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

// Peer latency monitoring
app.get('/api/latency', async (req, res) => {
  try {
    const peers = await callRpc('getpeerinfo');
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

    console.log('[API /api/latency] Latency info sent');

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

app.get('/api/rewards', async (req, res) => {
  try {
    const blockchainInfo = await callRpc('getblockchaininfo');
    const blockCount = blockchainInfo.blocks;

    const rewardHistory = [];
    let height = 0;
    const currentHeight = blockCount;
    let blockReward = 3.125;

    const totalRewards = blockCount * blockReward;
    const rewardRate = blockReward * 144; // Example: 144 blocks/day

    while (height <= currentHeight && blockReward >= 0.00000001) {
      rewardHistory.push({
        height,
        reward: blockReward,
        label: `Block ${height}`,
      });

      for (let i = 1; i < 210000 && height + i <= currentHeight; i += 10000) {
        rewardHistory.push({
          height: height + i,
          reward: blockReward,
          label: `Block ${height + i}`,
        });
      }
      blockReward /= 2;
      height += 210000;
    }
    console.log('[API /api/rewards] Sent reward stats');
    console.log(
      '[API /api/rewards] blockCount:',
      blockCount,
      'blockReward:',
      blockReward,
      'totalRewards:',
      totalRewards,
      'rewardRate:',
      rewardRate
    );

    res.json({
      rewardHistory,
      blockCount,
      blockReward,
      totalRewards,
      rewardRate,
      unit: 'BTC',
    });
  } catch (err) {
    console.error('[Rewards] Error:', err.message);
    res.status(500).json({ error: 'Failed to fetch reward data' });
  }
});

app.listen(PORT, () => {
  console.log(` Server running at http://localhost:${PORT}`);
});
