import axios from 'axios';

let rewardHistory = [];

export async function fetchReward() {
  try {
    const { data: blocks } = await axios.get(
      `${process.env.MEMPOOL_URL}/api/blocks`
    );
    const latestBlock = blocks[0];
    const { data: txs } = await axios.get(
      `${process.env.MEMPOOL_URL}/api/block/${latestBlock.id}/txs`
    );
    const coinbaseTx = txs[0];
    const rewardSats = coinbaseTx.vout.reduce(
      (sum, vout) => sum + vout.value,
      0
    );
    const rewardBTC = rewardSats / 1e8;
    const { data: priceData } = await axios.get(
      'https://api.coingecko.com/api/v3/simple/price?ids=bitcoin&vs_currencies=usd'
    );
    const btcPriceUSD = priceData.bitcoin.usd;
    const rewardInfo = {
      height: latestBlock.height,
      timestamp: new Date(latestBlock.timestamp * 1000).toISOString(),
      rewardBTC,
      rewardUSD: parseFloat((rewardBTC * btcPriceUSD).toFixed(2)), // Convert to number
    };
    const lastEntry = rewardHistory[rewardHistory.length - 1];
    if (!lastEntry || lastEntry.height !== rewardInfo.height) {
      rewardHistory.push(rewardInfo);
      if (rewardHistory.length > 30) {
        rewardHistory = rewardHistory.slice(-30);
      }
      console.log('NEW Block added to history:', rewardInfo);
    } else {
      console.log('Block already in history, skipping duplicate');
    }
    return rewardHistory;
  } catch (err) {
    console.error('Error fetching latest block reward:', err.message);
    return rewardHistory;
  }
}
