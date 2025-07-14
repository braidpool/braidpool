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
  const ip = req.query.ip || MINER_DEVICE_URL;
  const url = `http://${ip}/api/system/info`;

  try {
    const response = await fetch(url);
    if (!response.ok) {
      throw new Error(`Device at ${ip} returned ${response.status}`);
    }

    const json = await response.json();
    res.json(json);
  } catch (err) {
    console.error(`Failed to fetch from ${ip}:`, err);
    res
      .status(500)
      .json({ error: 'Could not connect to the miner at that IP' });
  }
});

app.listen(PORT, () => {
  console.log(`Proxy running on http://localhost:${PORT}`);
});
