import axios from 'axios';

export async function fetchPoolInfo() {
  try {
    const [poolInfoResponse, poolHashResponse] = await Promise.all([
      axios.get(`${process.env.MEMPOOL_URL}/api/v1/mining/pools/1w`),
      axios.get(`${process.env.MEMPOOL_URL}/api/v1/mining/hashrate/pools/1w`),
    ]);

    const poolInfoData = poolInfoResponse.data.pools;
    const poolHashData = poolHashResponse.data;
    const formatPoolSlug = (name) => {
      return name.toLowerCase().replace(/\s+/g, '').replace(/\./g, '');
    };

    const structuredData = await Promise.all(
      poolInfoData.map(async (pool) => {
        const slug = formatPoolSlug(pool.name);
        const matchingHash = poolHashData.find(
          (hash) => hash.poolName.toLowerCase() === pool.name.toLowerCase()
        );
        let latestBlockHeight = 'N/A';
        let poolLink = 'N/A';
        try {
          const blockRes = await axios.get(
            `${process.env.MEMPOOL_URL}/api/v1/mining/pool/${slug}/blocks`
          );
          const blocks = blockRes.data;
          if (blocks.length > 0) {
            latestBlockHeight = blocks[0].height;
          }
        } catch (err) {
          console.warn(
            `Block fetch failed for "${pool.name}" [${slug}]: ${err.message}`
          );
        }

        try {
          const extraRes = await axios.get(
            `${process.env.MEMPOOL_URL}/api/v1/mining/pool/${slug}`
          );
          const extraData = extraRes.data;
          poolLink = extraData.pool?.link ?? 'N/A';
        } catch (err) {
          console.warn(
            `Extra info fetch failed for "${pool.name}" [${slug}]: ${err.message}`
          );
        }

        return {
          rank: pool.rank,
          pool: pool.name,
          hashrate: matchingHash?.avgHashrate ?? 'N/A',
          blocks: pool.blockCount,
          avgHealth: `${pool.avgMatchRate}%`,
          avgBlockFees: `${parseFloat(pool.avgFeeDelta).toFixed(8)} BTC`,
          emptyBlocks: pool.emptyBlocks,
          latestBlockHeight,
          poolLink,
        };
      })
    );

    console.log(structuredData);
    return structuredData;
  } catch (error) {
    console.error('Failed to fetch pool info:', error.message);
    return null;
  }
}
