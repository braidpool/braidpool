// src/components/NodeHealth/backend/nodeApi.ts
import axios from 'axios';

const BASE_URL = 'http://localhost:3001/api/node';

const fetchNodeData = async (method: string) => {
  const res = await axios.post(`${BASE_URL}/${method}`);
  return res.data.result;
};

export const getBlockchainInfo = async () => {
  return fetchNodeData('getblockchaininfo');
};

export const getPeerInfo = async () => {
  return fetchNodeData('getpeerinfo');
};

export const getNetworkInfo = async () => {
  return fetchNodeData('getnetworkinfo');
};

export const getMempoolInfo = async () => {
  return fetchNodeData('getmempoolinfo');
};

export const getNetTotals = async () => {
  return fetchNodeData('getnettotals');
};
