import { WebSocketServer } from 'ws';
import dotenv from 'dotenv';
import fetchBitcoinPrices from './utils/fetchBitcoinPrices.js';
import fetchGlobalCryptoData from './utils/fetchGlobalData.js';
import { fetchHashrateStats } from './utils/fetchHashrate.js';
import { fetchLatencyData } from './utils/fetchLatency.js';
import { fetchReward } from './utils/fetchRewards.js';
import { handleWebSocketConnection } from './ws/handleWebSocketConnection.js';
import { fetchBlockDetails } from './utils/fetchBlockDetails.js';
import { fetchAllNodeData } from './utils/fetchBlockChainInfo.js';

dotenv.config();

const PORT = process.env.WS_PORT || 5000;
const wss = new WebSocketServer({ port: PORT });

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

  fetchReward(wss).catch((err) =>
    console.error('[Server] fetchReward failed:', err)
  );
  sendNodeHealthData().catch((err) =>
    console.error('[Server] fetchNodeHealth failed ', err)
  );
}, 10000); // 10-second interval

console.log(`WebSocket server running on ws://localhost:${PORT}`);
