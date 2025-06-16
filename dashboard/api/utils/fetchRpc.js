import axios from 'axios';

export async function callRpc({ url, user, pass, method, params = [] }) {
  try {
    const response = await axios.post(
      url,
      {
        jsonrpc: '1.0',
        id: 'rpc-call',
        method,
        params,
      },
      {
        auth: { username: user, password: pass },
        headers: { 'Content-Type': 'text/plain' },
      }
    );
    return response.data.result;
  } catch (err) {
    console.error(
      `[callRpc] Error calling ${method}:`,
      err?.response?.data || err.message
    );
    throw err;
  }
}
