import { rpcWithEnv } from './rpcWithEnv.js';

async function getBlockchainInfo() {
  return rpcWithEnv({ method: 'getblockchaininfo' });
}
async function getPeerInfo() {
  return rpcWithEnv({ method: 'getpeerinfo' });
}
async function getNetworkInfo() {
  return rpcWithEnv({ method: 'getnetworkinfo' });
}
async function getMempoolInfo() {
  return rpcWithEnv({ method: 'getmempoolinfo' });
}
async function getNetTotals() {
  return rpcWithEnv({ method: 'getnettotals' });
}

export async function fetchAllNodeData() {
  try {
  const [blockchain, peers, network, mempool, totals] = await Promise.all([
    getBlockchainInfo(),
    getPeerInfo(),
    getNetworkInfo(),
    getMempoolInfo(),
    getNetTotals(),
  ]);

  const result = {
    type: 'node_health_data',
    data: {
      blockchainInfo: blockchain,
      peerInfo: peers,
      networkInfo: network,
      mempoolInfo: mempool,
      netTotals: totals,
      lastUpdated: new Date().toISOString(),
    },
  };

  return result;
  }catch(error){
    console.error("Failed to fetch node data:" ,error);
    throw error;
  }
 
}


