import { rpcWithEnv } from './rpcWithEnv.js';

let lastDifficulty = null;
let lastDiffTime = 0;
const MIN_DISPLAYABLE_HASHRATE_EH = 0.005;

export async function fetchHashrateStats(wss) {
  try {
    const startTime = Date.now();
    const now = startTime;

    if (!lastDifficulty || now - lastDiffTime > 30_000) {
      lastDifficulty = await rpcWithEnv({ method: 'getdifficulty' });
      lastDiffTime = now;
    }

    const hashrate = await rpcWithEnv({ method: 'getnetworkhashps' });
    const hashrateEH = hashrate / 1e18;
    const normalizedHashrateEH =
      hashrateEH < MIN_DISPLAYABLE_HASHRATE_EH ? 0 : hashrateEH;
    const timestamp = now;

    const payload = {
      type: 'hashrate_data',
      data: {
        hashrate: normalizedHashrateEH,
        timestamp: timestamp,
        networkDifficulty: lastDifficulty / 1e12,
      },
    };
    console.log('Hashrate', payload.data);

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
