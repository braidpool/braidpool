import {
  getBlockchainInfo,
  getPeerInfo,
  getMempoolInfo,
  getNetworkInfo,
  getNetTotals,
} from './rpcMethods.js';

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
