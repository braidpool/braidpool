import axios from 'axios';

const BASE_URL = 'http://localhost:3001/api/node';

const fetchNodeData = async (method: string) => {
  const res = await axios.post(`${BASE_URL}/${method}`);
  return res.data.result;
};

export const getBlockTransactions = async (blockHash: string) => {
  const res = await axios.get(`http://localhost:3001/api/beads/${blockHash}/transactions`);
  return res.data; // Should be an array of transactions
};

// ✅ Add this to fetch hashrate and latency
export const getNodeStats = async () => {
  const res = await axios.get('http://localhost:3001/api/stats');
  return res.data; // { hashrate, latency, timestamp }
};

export const getLatencyChartData = async () => {
  const res = await axios.get('http://localhost:3001/api/latency');
  return res.data.chartData; // Array of { value, label, date }
};