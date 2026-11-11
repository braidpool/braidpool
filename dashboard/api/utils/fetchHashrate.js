import { rpcWithEnv } from './rpcWithEnv.js';

// Difficulty changes roughly every two weeks, so it is cached between broadcasts.
const DIFFICULTY_TTL_MS = 30_000;

let lastDifficulty = null;
let lastDiffTime = 0;

// Broadcasts the network difficulty (in T) to all connected clients.
export async function fetchHashrateStats(wss) {
  try {
    const now = Date.now();

    if (!lastDifficulty || now - lastDiffTime > DIFFICULTY_TTL_MS) {
      lastDifficulty = await rpcWithEnv({ method: 'getdifficulty' });
      lastDiffTime = now;
    }

    const payload = {
      type: 'hashrate_data',
      data: {
        networkDifficulty: lastDifficulty / 1e12,
        timestamp: now,
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error(
      '[WebSocket] Failed to fetch or send difficulty:',
      err.message
    );
  }
}
