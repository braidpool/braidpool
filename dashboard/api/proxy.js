import express from 'express';
import fetch from 'node-fetch';
import cors from 'cors';
import dotenv from 'dotenv';

dotenv.config();

const app = express();
const PORT = process.env.PORT || 5000;
const MINER_DEVICE_URL = process.env.MINER_DEVICE_URL;

app.use(cors());

app.get('/api/miners', async (req, res) => {
  try {
    const response = await fetch(MINER_DEVICE_URL );
    const json = await response.json();
    res.json(json);
  } catch (err) {
    console.error('Proxy fetch failed:', err);
    res.status(500).json({ error: 'Failed to fetch miner data' });
  }
});

app.listen(PORT, () => {
  console.log(`Proxy running on http://localhost:${PORT}`);
});
