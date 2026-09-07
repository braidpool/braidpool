import axios from 'axios';

export let latestMempoolPayload = null;

const FIAT_CURRENCIES = [
  'USD',
  'EUR',
  'JPY',
  'GBP',
  'CAD',
  'AUD',
  'CHF',
  'INR',
  'KRW',
  'BRL',
  'HKD',
  'SGD',
];

let lastKnownBlockFeeCurrencyRates = {};

function normalizeDecimalString(value) {
  let raw = String(value).trim();
  if (!raw) return null;

  if (raw.startsWith('.')) {
    raw = '0' + raw;
  } else if (raw.startsWith('-.') || raw.startsWith('+.')) {
    raw = raw[0] + '0.' + raw.slice(2);
  }

  const match = raw.match(/^([+-]?)(\d+)(?:\.(\d+))?$/);
  if (!match) return null;

  const sign = match[1] === '-' ? '-' : '';
  const intPart = match[2].replace(/^0+(?=\d)/, '') || '0';
  const fracPart = (match[3] || '').replace(/0+$/, '');

  if (fracPart.length === 0) {
    return `${sign}${intPart}`;
  }

  return `${sign}${intPart}.${fracPart}`;
}

function decimalToScaledInt(value) {
  const normalized = normalizeDecimalString(value);
  if (!normalized) return null;

  const negative = normalized.startsWith('-');
  const unsigned = normalized.replace(/^[+-]/, '');
  const [intPart, fracPart = ''] = unsigned.split('.');
  const digits = `${intPart}${fracPart}`;

  if (!/^\d+$/.test(digits)) return null;

  let intValue = BigInt(digits || '0');
  if (negative) intValue = -intValue;

  return { intValue, scale: fracPart.length };
}

function scaledIntToDecimalString(intValue, scale) {
  const negative = intValue < 0n;
  let digits = (negative ? -intValue : intValue).toString();

  if (scale > 0) {
    if (digits.length <= scale) {
      digits = digits.padStart(scale + 1, '0');
    }

    const split = digits.length - scale;
    const intPart = digits.slice(0, split);
    const fracPart = digits.slice(split).replace(/0+$/, '');
    const body = fracPart ? `${intPart}.${fracPart}` : intPart;
    return negative ? `-${body}` : body;
  }

  return negative ? `-${digits}` : digits;
}

function satsToBtcDecimalString(sats) {
  const satsNum = Number(sats);
  if (!Number.isFinite(satsNum)) return null;

  const satsInt = BigInt(Math.round(satsNum));
  let str = scaledIntToDecimalString(satsInt, 8);

  if (!str.includes('.')) {
    str += '.00000000';
  } else {
    const [, frac] = str.split('.');
    if (frac.length < 8) {
      str += '0'.repeat(8 - frac.length);
    }
  }

  return str;
}

function convertSatsToFiatDecimalString(sats, rateDecimal) {
  const rateScaled = decimalToScaledInt(rateDecimal);
  if (!rateScaled) return null;

  const satsNum = Number(sats);
  if (!Number.isFinite(satsNum)) return null;

  const satsInt = BigInt(Math.round(satsNum));
  const multiplied = satsInt * rateScaled.intValue;

  return scaledIntToDecimalString(multiplied, 8 + rateScaled.scale);
}

export function __resetBlockFeeCurrencyRateCache() {
  lastKnownBlockFeeCurrencyRates = {};
}

async function getBlockFeeCurrencyRates() {
  try {
    const rates = {};
    let unifiedSuccess = false;

    const unifiedUrl =
      process.env.BITCOIN_EXCHANGE_RATES_URL ||
      'https://api.coinbase.com/v2/exchange-rates?currency=BTC';

    try {
      const unifiedRes = await axios.get(unifiedUrl);
      const allRates = unifiedRes.data?.data?.rates;

      if (allRates) {
        for (const currency of FIAT_CURRENCIES) {
          const rawAmount = allRates[currency];
          const normalized = normalizeDecimalString(rawAmount);

          if (normalized !== null) {
            rates[currency] = normalized;
          } else {
            if (typeof lastKnownBlockFeeCurrencyRates[currency] === 'string') {
              rates[currency] = lastKnownBlockFeeCurrencyRates[currency];
              console.warn(
                `[getBlockFeeCurrencyRates] Non-finite unified rate for ${currency}; using last known value.`
              );
            } else {
              console.warn(
                `[getBlockFeeCurrencyRates] Non-finite unified rate for ${currency}; omitting currency.`
              );
            }
          }
        }
        unifiedSuccess = true;
      }
    } catch (unifiedErr) {
      console.warn(
        `[getBlockFeeCurrencyRates] Unified rates API failed, falling back to individual requests: ${unifiedErr.message}`
      );
    }

    if (!unifiedSuccess) {
      const results = await Promise.allSettled(
        FIAT_CURRENCIES.map((c) =>
          axios.get(
            `${process.env.BITCOIN_PRICE_URL}${c}${process.env.BITCOIN_PRICE_URL_SUFFIX}`
          )
        )
      );

      results.forEach((result, index) => {
        const currency = FIAT_CURRENCIES[index];

        if (result.status === 'fulfilled') {
          const rawAmount = result.value?.data?.data?.amount;
          const normalized = normalizeDecimalString(rawAmount);

          if (normalized !== null) {
            rates[currency] = normalized;
            return;
          }

          if (typeof lastKnownBlockFeeCurrencyRates[currency] === 'string') {
            rates[currency] = lastKnownBlockFeeCurrencyRates[currency];
            console.warn(
              `[getBlockFeeCurrencyRates] Non-finite rate for ${currency}; using last known value.`
            );
            return;
          }

          console.warn(
            `[getBlockFeeCurrencyRates] Non-finite rate for ${currency}; omitting currency.`
          );
          return;
        }

        const reasonMessage = result.reason?.message || result.reason;

        if (typeof lastKnownBlockFeeCurrencyRates[currency] === 'string') {
          rates[currency] = lastKnownBlockFeeCurrencyRates[currency];
          console.warn(
            `[getBlockFeeCurrencyRates] Failed to fetch ${currency}; using last known value: ${reasonMessage}`
          );
          return;
        }

        console.error(
          `[getBlockFeeCurrencyRates] Failed to fetch ${currency}; omitting currency: ${reasonMessage}`
        );
      });
    }

    lastKnownBlockFeeCurrencyRates = {
      ...lastKnownBlockFeeCurrencyRates,
      ...rates,
    };

    return rates;
  } catch (err) {
    console.error(
      '[getBlockFeeCurrencyRates] Unexpected failure:',
      err.message
    );
    return { ...lastKnownBlockFeeCurrencyRates };
  }
}

export async function fetchMempoolStats() {
  try {
    const statsRes = await axios.get(`${process.env.MEMPOOL_URL}/api/mempool`);
    const feesRes = await axios.get(
      `${process.env.MEMPOOL_URL}/api/v1/fees/recommended`
    );
    const oneMinuteBlockDataRes = await axios.get(
      `${process.env.MEMPOOL_URL}/api/v1/mining/blocks/fee-rates/1m`
    );
    const blockfeesRes = await axios.get(
      `${process.env.MEMPOOL_URL}/api/v1/mining/blocks/fees/1w`
    );
    const btcRates = await getBlockFeeCurrencyRates();

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

    const convertFee = (sats) => {
      const txVBytes = 140; // Typical transaction size in vBytes
      const totalSats = sats * txVBytes;
      const feeBtc = satsToBtcDecimalString(totalSats);
      if (feeBtc === null) {
        return { sats_per_vbyte: sats, fee_btc: null };
      }

      const fee = { sats_per_vbyte: sats, fee_btc: feeBtc };
      for (const [currency, rate] of Object.entries(btcRates)) {
        const lowerCurr = currency.toLowerCase();

        // Total Tx Fee
        const convertedTotal = convertSatsToFiatDecimalString(totalSats, rate);
        if (convertedTotal !== null) {
          fee[`fee_${lowerCurr}`] = convertedTotal;
        }

        // Per vByte Rate Fee
        const convertedRate = convertSatsToFiatDecimalString(sats, rate);
        if (convertedRate !== null) {
          fee[`rate_${lowerCurr}_per_vbyte`] = convertedRate;
        }
      }
      return fee;
    };

    const blockFeesArray = blockfeesRes.data;
    const latestBlockFeeRaw =
      Array.isArray(blockFeesArray) && blockFeesArray.length > 0
        ? blockFeesArray[blockFeesArray.length - 1]
        : null;

    const blockfeeHistory = (() => {
      if (!latestBlockFeeRaw) return [];
      const feeBtc = satsToBtcDecimalString(latestBlockFeeRaw.avgFees);
      if (feeBtc === null) return [];

      const item = {
        height: latestBlockFeeRaw.avgHeight,
        time: new Date(
          (latestBlockFeeRaw.timestamp || 0) * 1000
        ).toLocaleTimeString(),
        btc: feeBtc,
      };
      for (const [currency, rate] of Object.entries(btcRates)) {
        const converted = convertSatsToFiatDecimalString(
          latestBlockFeeRaw.avgFees,
          rate
        );
        if (converted !== null) {
          item[currency.toLowerCase()] = converted;
        }
      }
      return [item];
    })();

    const totalFeeBtc = satsToBtcDecimalString(total_fee);
    if (totalFeeBtc === null) {
      throw new Error('Invalid total_fee value received from mempool API');
    }

    const mempool = { count, vsize, total_fee_btc: totalFeeBtc };
    for (const [currency, rate] of Object.entries(btcRates)) {
      const converted = convertSatsToFiatDecimalString(total_fee, rate);
      if (converted !== null) {
        mempool[`total_fee_${currency.toLowerCase()}`] = converted;
      }
    }

    const result = {
      mempool,
      next_block_fees: convertFee(fastestFee),
      fees: {
        high_priority: convertFee(fastestFee),
        medium_priority: convertFee(halfHourFee),
        standard_priority: convertFee(hourFee),
        economy: convertFee(economyFee),
        minimum: convertFee(minimumFee),
      },
      btc_price_usd: btcRates.USD ?? null,
      fee_distribution: feeDistribution,
      block_fee_history: blockfeeHistory,
    };

    latestMempoolPayload = {
      type: 'mempool_update',
      data: result,
      time: new Date().toLocaleString(),
    };

    return result;
  } catch (error) {
    console.error('[fetchMempoolStats] Failed to fetch:', error.message);
    return null;
  }
}
