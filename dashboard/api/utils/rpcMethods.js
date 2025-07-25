const { rpcWithEnv } = require('./rpcWithEnv.js');

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
module.exports ={getBlockchainInfo,getMempoolInfo,getNetworkInfo,getNetTotals,getPeerInfo}