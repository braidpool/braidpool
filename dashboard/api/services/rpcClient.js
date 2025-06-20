import axios from 'axios';
import { BRAIDPOOL_URL, RPC_USER, RPC_PASS } from '../config/env.js';

export async function callRpcMethod(method) {
  const response = await axios.post(
    BRAIDPOOL_URL,
    {
      jsonrpc: '1.0',
      id: 'proxy',
      method,
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
  return response.data;
}
