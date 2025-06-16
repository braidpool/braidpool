import express from 'express';

import { rpcWithEnv } from '../utils/rpcWithEnv.js';
const router = express.Router();
router.get('/:blockHash/transactions', async (req, res) => {
  try {
    const block = await rpcWithEnv({
      method: 'getblock',
      params: [req.params.blockHash, 2],
    });
    res.json(block.tx);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

export default router;
