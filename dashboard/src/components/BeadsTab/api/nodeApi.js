import axios from 'axios';

const BASE_URL = 'http://localhost:3001/api/node';

const fetchNodeData = async (method) => {
  const res = await axios.post(`${BASE_URL}/${method}`);
  return res.data.result;
};

export const getBlockTransactions = async (blockHash) => {
  const res = await axios.get(
    `http://localhost:3001/api/beads/${blockHash}/transactions`
  );
  return res.data;
};

export const getNodeStats = async () => {
  const res = await axios.get('http://localhost:3001/api/stats');
  return res.data;
};

export const getLatencyChartData = async () => {
  const res = await axios.get('http://localhost:3001/api/latency');
  return res.data.chartData;
};
export const getBlockReward = async () => {
  const res = await axios.get('http://localhost:3001/api/rewards');
  return res.data;
};
