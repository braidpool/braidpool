import axios from 'axios';

const HISTORIC_SUFFIX = '/historic?days=1';
const currencies = ['USD', 'EUR', 'JPY'];

async function fetchBitcoinPrices(BASE_URL, SPOT_SUFFIX) {
  const prices = {};

  try {
    for (const currency of currencies) {
      const spotUrl = `${BASE_URL}${currency}${SPOT_SUFFIX}`;
      const historicUrl = `${BASE_URL}${currency}${HISTORIC_SUFFIX}`;

      // 1. Fetch spot price
      const spotRes = await axios.get(spotUrl);
      const current = parseFloat(spotRes.data.data.amount);

      // 2. Fetch 24h historic prices
      const historicRes = await axios.get(historicUrl);
      const historicPrices = historicRes.data.data.prices.map((p) =>
        parseFloat(p.price)
      );

      const high24h = Math.max(...historicPrices);
      const low24h = Math.min(...historicPrices);

      prices[currency] = { current, high24h, low24h };
    }

    return prices;
  } catch (error) {
    console.error('Error fetching BTC price data:', error.message);
    return null;
  }
}

export default fetchBitcoinPrices;
