import axios from 'axios';

export async function callRpc({ url, user, pass, method, params = [] }) {
  const payload = {
    jsonrpc: '1.0',
    id: 'rpc-call',
    method,
    params,
  };

  const response = await axios.post(url, payload, {
    auth: { username: user, password: pass },
    headers: { 'Content-Type': 'application/json' },
  });

  if (response.data.error) {
    throw new Error(JSON.stringify(response.data.error));
  }

  return response.data.result;
}
