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

app.use(
  cors({
    origin: 'http://localhost:3000',
    credentials: true,
  })
);

app.use(express.json());

async function callRpc(method, params = []) {
  const res = await axios.post(
    BRAIDPOOL_URL,
    {
      jsonrpc: '1.0',
      id: 'proxy',
      method,
      params,
    },
    {
      auth: {
        username: RPC_USER,
        password: RPC_PASS,
      },
      headers: { 'Content-Type': 'text/plain' },
    }
  );
  return res.data.result;
}

app.use('/api/node/:endpoint', async (req, res) => {
  try {
    const endpoint = req.params.endpoint;
    console.log(`[Proxy] Received request for endpoint: ${endpoint}`);

    const response = await axios.post(
      BRAIDPOOL_URL,
      {
        jsonrpc: '1.0',
        id: 'proxy',
        method: endpoint,
        params: [],
      },
      {
        auth: {
          username: RPC_USER,
          password: RPC_PASS,
        },
        headers: {
          'Content-Type': 'text/plain',
        },
      }
    );

    console.log(`[Proxy] RPC call successful for ${endpoint}`);
    res.json(response.data);
  } catch (error) {
    if (error?.response?.data) {
      console.error(
        '[Proxy] Proxy error (response.data):',
        error.response.data
      );
    } else {
      console.error('[Proxy] Proxy error:', error);
    }
    res.status(500).json({ error: 'Internal server error' });
  }
});
app.get('/api/beads/:blockHash/transactions', async (req, res) => {
  try {
    const block = await callRpc('getblock', [req.params.blockHash, 2]);
    res.json(block.tx); 
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.listen(PORT, () => {
  console.log(`Proxy server running on http://localhost:${PORT}`);
});
app.get('/api/stats', async (req, res) => {
  const startTime = Date.now();

  try {
    const [hashrate, difficulty] = await Promise.all([
      callRpc('getnetworkhashps'),
      callRpc('getdifficulty'),
    ]);
    const endTime = Date.now();
    const latency = endTime - startTime;
    const timestamp = new Date().toISOString();


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
  averageHashrate: avgHashrate,
  peakHashrate: peakHashrate,
  networkDifficulty: difficulty,
}) ;
}catch (err) {
    console.error('[Stats] Error fetching hashrate/latency:', err.message);
    res.status(500).json({ error: 'Failed to fetch stats' });
  }
});
app.get('/api/latency', async (req, res) => {
  try {
    const peers = await callRpc('getpeerinfo');

    const pings = peers
      .map((peer) => peer.pingtime)
      .filter((t) => typeof t === 'number');

    const avgPing = pings.length
      ? pings.reduce((a, b) => a + b, 0) / pings.length
      : 0;
    const peakLatency = pings.length
      ? Math.max(...pings) * 1000
      : 0;
    const peerCount = pings.length;

    const latency = Math.round(avgPing * 1000); 
    const timestamp = new Date().toISOString();

    latencyHistory.push({
      value: latency,
      label: new Date(timestamp).toLocaleString(),
      date: timestamp,
    });

    if (latencyHistory.length > 100) latencyHistory.shift();
    console.log(
      '[API /api/latency] Response:',
      { chartData: latencyHistory },
      'avgLatency(ms):', (avgPing * 1000).toFixed(2),
      'peakLatency(ms):', peakLatency.toFixed(2),
      'peerCount:', peerCount
    );

    res.json({
      chartData: latencyHistory,
      averageLatency: (avgPing * 1000).toFixed(2), 
      peakLatency: peakLatency.toFixed(2),         
      peerCount,
    });
  } catch (err) {
    console.error('[Latency] Error:', err.message);
    res.status(500).json({ error: 'Failed to fetch latency' });
  }
});

