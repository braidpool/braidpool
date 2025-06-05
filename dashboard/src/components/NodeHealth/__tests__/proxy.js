import 'dotenv/config'
import express from 'express';
import axios from 'axios';
import cors from 'cors';

const app = express();
const PORT = process.env.PORT || 3001;
const BRAIDPOOL_URL = process.env.BRAIDPOOL_URL;; 

const RPC_USER = process.env.RPC_USER;
const RPC_PASS = process.env.RPC_PASS;

app.use(cors({
  origin: 'http://localhost:3000',
  credentials: true
}));

app.use(express.json());

app.use('/api/node/:endpoint', async (req, res) => {
  try {
    const endpoint = req.params.endpoint;
    console.log(`[Proxy] Received request for endpoint: ${endpoint}`);

    const response = await axios.post(
      BRAIDPOOL_URL,
      {
        jsonrpc: "1.0",
        id: "proxy",
        method: endpoint,
        params: []
      },
      {
        auth: {
          username: RPC_USER,
          password: RPC_PASS
        },
        headers: {
          'Content-Type': 'text/plain'
        }
      }
    );

    console.log(`[Proxy] RPC call successful for ${endpoint}`);
    res.json(response.data);
  } catch (error) {
    if (error?.response?.data) {
      console.error('[Proxy] Proxy error (response.data):', error.response.data);
    } else {
      console.error('[Proxy] Proxy error:', error);
    }
    res.status(500).json({ error: 'Internal server error' });
  }
});

app.listen(PORT, () => {
  console.log(`Proxy server running on http://localhost:${PORT}`);
});
