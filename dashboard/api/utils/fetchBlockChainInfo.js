import { rpcWithEnv } from './rpcWithEnv.js';

async function getBlockchainInfo() {
  try {
    return await rpcWithEnv({ method: 'getblockchaininfo' });
  } catch (error) {
    console.error('Error in getBlockchainInfo:', error);
    throw error;
  }
}

async function getPeerInfo() {
  try {
    return await rpcWithEnv({ method: 'getpeerinfo' });
  } catch (error) {
    console.error('Error in getPeerInfo:', error);
    throw error;
  }
}

async function getNetworkInfo() {
  try {
    return await rpcWithEnv({ method: 'getnetworkinfo' });
  } catch (error) {
    console.error('Error in getNetworkInfo:', error);
    throw error;
  }
}

async function getMempoolInfo() {
  try {
    return await rpcWithEnv({ method: 'getmempoolinfo' });
  } catch (error) {
    console.error('Error in getMempoolInfo:', error);
    throw error;
  }
}

async function getNetTotals() {
  try {
    return await rpcWithEnv({ method: 'getnettotals' });
  } catch (error) {
    console.error('Error in getNetTotals:', error);
    throw error;
  }
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

    const data = {
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
    return data;

  } catch (error) {
    console.error('Failed to fetch all node data:', error);
    throw error;
  }
}
