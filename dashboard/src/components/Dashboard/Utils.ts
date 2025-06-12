import axios from 'axios';

// via mempool api
export const getBlockInfo = async (hash: string): Promise<any> => {
  try {
    const response = await axios.get(`http://localhost:8999/api/v1/block/${hash}`);
    console.log(response.data);
    return response.data;
  } catch (error) {
    console.error('Error fetching block info:', error);
    throw error;
  }
};

export const fetchPreviousBlocks = async () => {
  try {
    const response = await fetch('http://localhost:8999/api/v1/blocks');
    if (!response.ok) throw new Error('Network response was not ok');
    const data = await response.json();
    return data;
  } catch (err) {
    console.error('Failed to fetch previous blocks', err);
    throw err;
  }
};
