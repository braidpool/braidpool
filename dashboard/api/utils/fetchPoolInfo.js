import axios from 'axios';

export async function fetchPoolInfo() {
  try {
    const [poolInfoResponse, poolHashResponse] = await Promise.all([
      axios.get(`${process.env.MEMPOOL_API_URL}/api/v1/mining/pools/1w`),
      axios.get(`${process.env.MEMPOOL_API_URL}/api/v1/mining/hashrate/pools/1w`), 
    ]);

    const poolInfoData = poolInfoResponse.data.pools;
    const poolHashData = poolHashResponse.data;

    const structuredData = poolInfoData.map((pool) => {
      const matchingHash = poolHashData.find(
        (hash) => hash.poolName.toLowerCase() === pool.name.toLowerCase()
      );

      return {
        rank: pool.rank,
        pool: pool.name,
        hashrate: matchingHash?.avgHashrate ?? 'N/A',
        blocks: pool.blockCount,
        avgHealth: `${pool.avgMatchRate}%`,
        avgBlockFees: `${parseFloat(pool.avgFeeDelta).toFixed(8)} BTC`,
        emptyBlocks: pool.emptyBlocks,
        
      };
    });

    return structuredData;
    
  } catch (error) {
    console.error('Failed to fetch pool info:', error.message);
    return null;
  }
}