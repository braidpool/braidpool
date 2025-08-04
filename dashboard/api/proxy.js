import express from 'express';
import fetch from 'node-fetch';
import cors from 'cors';

const app = express();
const PORT = 5001;
app.use(cors());

app.get('/api/miners', async (req, res) => {
  const ip = req.query.ip;
  if (!ip) {
    return res.status(400).json({ error: 'Miner IP address is required' });
  }

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
    res.status(500).json({ error: `Could not connect to the miner at ${ip}` });
  }
});

app.listen(PORT, () => {
  console.log(`Proxy running on http://localhost:${PORT}`);
});
