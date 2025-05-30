import axios from 'axios';

async function fetchGlobalCryptoData(CRYPTO_URL, currency = 'USD') {
  try {
    const response = await axios.get(`${CRYPTO_URL}/?convert=${currency}`);

    if (response.data && response.data.data) {
      return {
        marketCap: response.data.data.quotes[currency].total_market_cap,
        marketCapChange:
          response.data.data.quotes[currency]
            .total_market_cap_yesterday_percentage_change,
        activeCryptocurrencies: response.data.data.active_cryptocurrencies,
        activeMarkets: response.data.data.active_markets,
        bitcoinDominance: response.data.data.bitcoin_percentage_of_market_cap,
        lastUpdated: response.data.data.last_updated,
      };
    }
    throw new Error('Invalid response format');
  } catch (error) {
    console.error('Error fetching global crypto data:', error.message);
    return null;
  }
}

export default fetchGlobalCryptoData;
