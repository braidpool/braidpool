import { rpcWithEnv } from './rpcWithEnv.js';

const MAX_HISTORY_LENGTH = 288; 
let hashrateHistory = [];
let peakHashrate = 0;


let lastDifficulty = null;
let lastDiffTime = 0;

export async function fetchHashrateStats(wss) {
  try {
    const startTime = Date.now();

    const now = Date.now();
  
    if (!lastDifficulty || now - lastDiffTime > 30_000) {
      lastDifficulty = await rpcWithEnv({ method: 'getdifficulty' });
      lastDiffTime = now;
    }

  
    const hashrate = await rpcWithEnv({ method: 'getnetworkhashps' });
    const hashrateEH = hashrate / 1e18;

    const latency = Date.now() - startTime;
    const timestamp = new Date().toISOString();

    const historyEntry = {
      value: hashrateEH,
      date: timestamp,
      label: new Date(timestamp).toLocaleTimeString()
    };

    if (hashrateHistory.length >= MAX_HISTORY_LENGTH) {
      hashrateHistory.shift(); 
    }
    hashrateHistory.push(historyEntry);

    if (hashrateEH > peakHashrate) {
      peakHashrate = hashrateEH;
    }

    const poolDominance = ((hashrateEH / (hashrateEH * 10)) * 100).toFixed(2);

   
    const payload = {
      type: 'hashrate_update',
      data: {
        history: hashrateHistory,
        current: `${hashrateEH.toFixed(2)} EH/s`,
        peak: `${peakHashrate.toFixed(2)} EH/s`,
        dominance: `${poolDominance}%`,
         networkDifficulty: lastDifficulty,
        latency
      }
    };

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });

  } catch (err) {
    console.error('[WebSocket] Failed to fetch or send hashrate stats:', err.message);
  }
}
