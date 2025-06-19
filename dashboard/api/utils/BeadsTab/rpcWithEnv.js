import { callRpc } from './fetchRpc.js';

export function rpcWithEnv({ method, params = [] }) {
  return callRpc({
    url: process.env.BRAIDPOOL_URL,
    user: process.env.RPC_USER,
    pass: process.env.RPC_PASS,
    method,
    params,
  });
}
