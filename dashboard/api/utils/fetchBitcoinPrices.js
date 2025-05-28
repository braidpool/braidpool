import axios from 'axios';

async function fetchBitcoinPrices(BITCOIN_PRICE_URL, BITCOIN_PRICE_URL_SUFFIX) {
    const currencies = ["USD", "EUR", "JPY"];
    const prices = {};

    try {
        for (const currency of currencies) {
            const response = await axios.get(`${BITCOIN_PRICE_URL}${currency}${BITCOIN_PRICE_URL_SUFFIX}`);
            prices[currency] = response.data.data.amount;
        }
        return prices;
    } catch (error) {
        console.error("Error fetching BTC price:", error.message);
        return null;
    }
}

export default fetchBitcoinPrices;