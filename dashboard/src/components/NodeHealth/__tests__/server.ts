import axios from 'axios';
require('dotenv').config();
const BRAIDPOOL_URL = process.env.BRAIDPOOL_URL;
const RPC_USER = process.env.RPC_USER;
const RPC_PASS = process.env.RPC_PASS;
const PORT = process.env.PORT || 3001;
const forwardRequest = async (method: string): Promise<any> => {
  try {
    const response = await axios.post(
      BRAIDPOOL_URL,
      {
        jsonrpc: "1.0",
        id: "braidpool",
        method,
        params: [],
      },{
        auth: {
          username: RPC_USER,
          password: RPC_PASS,
        },
        headers: {
          'Content-Type': 'text/plain',
        },
      }
    );
    return response.data.result;
  } 
 catch (error) {
    if (error && typeof error === 'object' && 'response' in error && error.response && typeof error.response === 'object' && 'data' in error.response) {
    
      console.error(`Error calling ${method}:`, error.response.data);
    } else {
      console.error(`Error calling ${method}:`, error);
    }
    throw error;
  }
};

export const getBlockchainInfo = async () => forwardRequest('getblockchaininfo');
export const getPeerInfo = async () => forwardRequest('getpeerinfo');
export const getNetworkInfo = async () => forwardRequest('getnetworkinfo');
export const getMempoolInfo = async () => forwardRequest('getmempoolinfo');
export const getNetTotals = async () => forwardRequest('getnettotals');
