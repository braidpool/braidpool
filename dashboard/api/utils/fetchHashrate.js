import { rpcWithEnv } from './rpcWithEnv.js';

const statsHistory = [];

export async function fetchHashrateStats(wss) {
  try {
    const startTime = Date.now();

    const [hashrate, difficulty] = await Promise.all([
      rpcWithEnv({ method: 'getnetworkhashps' }),
      rpcWithEnv({ method: 'getdifficulty' }),
    ]);

    const latency = Date.now() - startTime;
    const timestamp = new Date().toISOString();

    const payload = {
      type: 'hashrate_update',
      data: {
        latestStat: {
          value: hashrate,
          label: new Date(timestamp).toLocaleString(),
          date: timestamp,
          latency,
        },

        networkDifficulty: difficulty,
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error(
      '[WebSocket] Failed to fetch or send hashrate stats:',
      err.message
    );
  }
}
