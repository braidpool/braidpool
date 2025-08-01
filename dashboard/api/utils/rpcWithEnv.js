import { callRpc } from './fetchRpc.js';

export function rpcWithEnv({ method, params = [] }) {
  const url = process.env.BRAIDPOOL_URL;
  const user = process.env.RPC_USER;
  const pass = process.env.RPC_PASS;

  if (!url || !user || !pass) {
    console.error('Missing required RPC environment variables');
    throw new Error('Missing BRAIDPOOL_URL, RPC_USER, or RPC_PASS');
  }

  try {
    return callRpc({
      url,
      user,
      pass,
      method,
      params,
    });
  } catch (error) {
    console.error(`RPC call failed: ${method}`, error);
    throw error;
  }
}
