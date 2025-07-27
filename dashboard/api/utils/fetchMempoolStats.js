import axios from 'axios';

export async function fetchMempoolStats() {
  try {
    const statsRes = await axios.get(`${process.env.MEMPOOL_STATS_URL}`);
    const feesRes = await axios.get(`${process.env.FEE_RECOMMENDED_URL}`);
    const priceRes = await axios.get(`${process.env.BTC_PRICE_URL}`);
    const oneMinuteBlockDataRes = await axios.get(
      `${process.env.ONE_MIN_BLOCK_FEE_URL}`
    );
    const blockfeesRes = await axios.get(
      `${process.env.BLOCK_FEES_HISTORY_URL}`
    );

    const data = oneMinuteBlockDataRes.data;
    const latestBlock =
      Array.isArray(data) && data.length > 0 ? data[data.length - 1] : null;

    const feeDistribution = {
      min: latestBlock?.avgFee_0,
      '10th': latestBlock?.avgFee_10,
      '25th': latestBlock?.avgFee_25,
      median: latestBlock?.avgFee_50,
      '75th': latestBlock?.avgFee_75,
      '90th': latestBlock?.avgFee_90,
      max: latestBlock?.avgFee_100,
    };

    const { count, vsize, total_fee } = statsRes.data;
    const { fastestFee, halfHourFee, hourFee, economyFee, minimumFee } =
      feesRes.data;

    const btcPriceUSD = parseFloat(priceRes.data.price);

    const convertFee = (sats) => {
      const feeBtc = sats / 1e8;
      const feeUsd = feeBtc * btcPriceUSD;

      return {
        sats_per_vbyte: sats,
        fee_btc: feeBtc,
        fee_usd: feeUsd,
      };
    };

    console.log('[blockfeesRes.data sample]', blockfeesRes.data?.[0]);
    console.log('[btcPriceUSD]', btcPriceUSD);

    const blockFeesArray = blockfeesRes.data;
    const latestBlockFeeRaw =
      Array.isArray(blockFeesArray) && blockFeesArray.length > 0
        ? blockFeesArray[blockFeesArray.length - 1]
        : null;

    const blockfeeHistory = latestBlockFeeRaw
      ? [
          {
            height: latestBlockFeeRaw.avgHeight,
            time: new Date(
              (latestBlockFeeRaw.timestamp || 0) * 1000
            ).toLocaleTimeString(),
            btc: latestBlockFeeRaw.avgFees / 1e8,
            usd: latestBlockFeeRaw.USD,
          },
        ]
      : [];

    return {
      mempool: {
        count,
        vsize,
        total_fee_btc: total_fee / 1e8,
        total_fee_usd: (total_fee / 1e8) * btcPriceUSD,
      },
      next_block_fees: convertFee(fastestFee),
      fees: {
        high_priority: convertFee(fastestFee),
        medium_priority: convertFee(halfHourFee),
        standard_priority: convertFee(hourFee),
        economy: convertFee(economyFee),
        minimum: convertFee(minimumFee),
      },
      btc_price_usd: btcPriceUSD,
      fee_distribution: feeDistribution,
      block_fee_history: blockfeeHistory, // ✅ Only contains the latest block
    };
  } catch (error) {
    console.error('[fetchMempoolStats] Failed to fetch:', error.message);
    return null;
  }
}
