import axios from 'axios';

export async function callRpc(
  { url, user, pass, method, params = [] },
  retries = 3,
  delay = 2000,
  timeout = 5000
) {
  const payload = {
    jsonrpc: '1.0',
    id: 'rpc-call',
    method,
    params,
  };

  for (let attempt = 1; attempt <= retries; attempt++) {
    try {
      const response = await axios.post(url, payload, {
        auth: { username: user, password: pass },
        headers: { 'Content-Type': 'application/json' },
        timeout,
      });

      if (response.data.error) {
        throw new Error(JSON.stringify(response.data.error));
      }

      return response.data.result;
    } catch (error) {
      if (attempt < retries) {
        console.warn(
          `RPC call failed (attempt ${attempt}): Retrying in ${delay}ms...`
        );
        await new Promise((res) => setTimeout(res, delay));
      } else {
        console.error(`RPC call failed after ${retries} attempts.`);
        throw error;
      }
    }
  }
}
