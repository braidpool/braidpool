import { WebSocketServer } from 'ws';
import dotenv from 'dotenv';
import express from 'express';
import cors from 'cors';
import fetchBitcoinPrices from './utils/fetchBitcoinPrices.js';
import fetchGlobalCryptoData from './utils/fetchGlobalData.js';
import { fetchHashrateStats } from './utils/fetchHashrate.js';
import { fetchLatencyData } from './utils/fetchLatency.js';
import { fetchReward } from './utils/fetchRewards.js';
import { handleWebSocketConnection } from './ws/handleWebSocketConnection.js';
import { fetchBlockDetails } from './utils/fetchBlockDetails.js';
import { fetchAllNodeData } from './utils/fetchBlockChainInfo.js';
import { fetchPoolInfo } from './utils/fetchPoolInfo.js';
import { fetchMempoolStats } from './utils/fetchMempoolStats.js';

dotenv.config();

const PORT = process.env.WS_PORT || 5000;

const app = express();
app.use(
  cors({
    origin: [
      'http://localhost:5173',
      'http://127.0.0.1:5173',
      'http://localhost:3000',
    ],
  })
);
app.use(express.json({ limit: '100kb' }));

app.post('/api/report-error', (req, res) => {
  const { error, stack, componentStack, timestamp } = req.body;

  // Basic payload validation to prevent log spam
  if (!error || typeof error !== 'string' || error.length > 5000) {
    return res
      .status(400)
      .json({ success: false, message: 'Invalid error payload' });
  }
  console.error('\n=============================================');
  console.error(`[Frontend Error Reported by UI] at ${timestamp}`);
  console.error(`Message: ${error}`);
  if (stack) console.error(`Stack: ${stack}`);
  if (componentStack) console.error(`Component Stack: ${componentStack}`);
  console.error('=============================================\n');
  res.status(200).json({ success: true, message: 'Team has been notified.' });
});

const server = app.listen(PORT, () => {
  console.log(`HTTP and WebSocket server running on port ${PORT}`);
});

const wss = new WebSocketServer({ server });

const BITCOIN_PRICE_URL = process.env.BITCOIN_PRICE_URL;
const BITCOIN_PRICE_URL_SUFFIX = process.env.BITCOIN_PRICE_URL_SUFFIX;
const CRYPTO_URL = process.env.CRYPTO_URL;

wss.on('connection', (ws) => handleWebSocketConnection(ws, wss));

// Send combined data to all connected WebSocket clients
async function sendDataToClients() {
  const [bitcoinPrice, globalCryptoData] = await Promise.all([
    fetchBitcoinPrices(BITCOIN_PRICE_URL, BITCOIN_PRICE_URL_SUFFIX),
    fetchGlobalCryptoData(CRYPTO_URL, 'USD'),
  ]);

  if (bitcoinPrice && globalCryptoData) {
    const data = {
      type: 'bitcoin_update',
      data: {
        price: bitcoinPrice,
        global_stats: {
          market_cap: globalCryptoData.marketCap,
          market_cap_change: globalCryptoData.marketCapChange,
          active_cryptocurrencies: globalCryptoData.activeCryptocurrencies,
          active_markets: globalCryptoData.activeMarkets,
          bitcoin_dominance: globalCryptoData.bitcoinDominance,
          last_updated: globalCryptoData.lastUpdated,
        },
        time: new Date().toLocaleString(),
      },
    };

    console.log('Broadcasting update:', data);

    wss.clients.forEach((client) => {
      if (client.readyState === client.OPEN) {
        client.send(JSON.stringify(data));
      }
    });
  }
}
async function sendNodeHealthData() {
  const nodeHealthData = await fetchAllNodeData();
  wss.clients.forEach((client) => {
    if (client.readyState === client.OPEN) {
      client.send(JSON.stringify(nodeHealthData));
    }
  });
}
async function sendPoolInfo() {
  try {
    const stats = await fetchPoolInfo();

    if (stats) {
      const mempoolData = {
        type: 'pool_update',
        data: stats,
        time: new Date().toLocaleString(),
      };

      wss.clients.forEach((client) => {
        if (client.readyState === client.OPEN) {
          client.send(JSON.stringify(mempoolData));
        }
      });
    }
  } catch (err) {
    console.error('[Server] fetchPoolStats failed:', err.message);
  }
}
async function sendReward() {
  try {
    const stats = await fetchReward();

    if (stats) {
      const mempoolData = {
        type: 'reward_update',
        data: stats,
        time: new Date().toLocaleString(),
      };

      wss.clients.forEach((client) => {
        if (client.readyState === client.OPEN) {
          client.send(JSON.stringify(mempoolData));
        }
      });
    }
  } catch (err) {
    console.error('[Server] Rewards failed:', err.message);
  }
}
async function sendMempoolData() {
  try {
    const stats = await fetchMempoolStats();

    if (stats) {
      const mempoolData = {
        type: 'mempool_update',
        data: stats,
        time: new Date().toLocaleString(),
      };

      wss.clients.forEach((client) => {
        if (client.readyState === client.OPEN) {
          client.send(JSON.stringify(mempoolData));
        }
      });
    }
  } catch (err) {
    console.error('[Server] fetchMempoolStats failed:', err.message);
  }
}

setInterval(() => {
  sendDataToClients().catch((err) =>
    console.error('[Server] sendDataToClients failed:', err)
  );

  fetchBlockDetails(wss).catch((err) =>
    console.error('[Server] fetchBlockDetails failed:', err)
  );

  fetchHashrateStats(wss).catch((err) =>
    console.error('[Server] fetchHashrateStats failed:', err)
  );

  fetchLatencyData(wss).catch((err) =>
    console.error('[Server] fetchLatencyData failed:', err)
  );

  sendReward();
  sendNodeHealthData().catch((err) =>
    console.error('[Server] fetchNodeHealth failed ', err)
  );
  sendPoolInfo();
  sendMempoolData();
}, 30000); // 30-second interval
