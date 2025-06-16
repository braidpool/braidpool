import express from 'express';
import { callRpcMethod } from '../services/rpcClient.js';

const router = express.Router();

router.post('/node/:endpoint', async (req, res) => {
  const endpoint = req.params.endpoint;
  console.log(`[Proxy] Received request for endpoint: ${endpoint}`);

  try {
    const data = await callRpcMethod(endpoint);
    console.log(`[Proxy] RPC call successful for ${endpoint}`);
    res.json(data);
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

export default router;
