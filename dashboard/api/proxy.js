import 'dotenv/config';
import express from 'express';
import cors from 'cors';

import statsRoutes from './routes/stats.js';
import latencyRoutes from './routes/latency.js';
import rewardsRoutes from './routes/rewards.js';
import beadRoutes from './routes/bead.js';
import { callRpc } from './utils/fetchRpc.js';
const app = express();
const PORT = process.env.PORT || 3001;

app.use(cors({ origin: 'http://localhost:3000', credentials: true }));
app.use(express.json());

app.use('/api/stats', statsRoutes);
app.use('/api/latency', latencyRoutes);
app.use('/api/rewards', rewardsRoutes);
app.use('/api/beads', beadRoutes);



app.use('/api/node/:endpoint', async (req, res) => {
  try {
    const { endpoint } = req.params;
    const result = await callRpc({
      url: process.env.BRAIDPOOL_URL,
      user: process.env.RPC_USER,
      pass: process.env.RPC_PASS,
      method: endpoint,
      params: req.body?.params || [],
    });
    res.json(result);
  } catch (error) {
    res.status(500).json({ error: 'Internal server error' });
  }
});

app.listen(PORT, () => {
  console.log(`Server running at http://localhost:${PORT}`);
});
