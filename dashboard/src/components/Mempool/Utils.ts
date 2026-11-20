import { Currency, CurrencyRates } from './Types';

export const CURRENCIES: Currency[] = ['BTC', 'USD', 'EUR', 'JPY'];

export function formatBtcAmount(
  btc: number | undefined,
  currency: Currency,
  rates: CurrencyRates | undefined
): string {
  if (typeof btc !== 'number' || isNaN(btc)) return '--';
  if (currency === 'BTC') return `${btc.toFixed(8)} BTC`;

  const rate = rates?.[currency];
  if (!rate) return '--';

  const value = btc * rate;
  // Per-vbyte fees are small; default precision would round them to whole cents or yen.
  return new Intl.NumberFormat('en-US', {
    style: 'currency',
    currency,
    ...(value < 100 && { minimumFractionDigits: 2, maximumFractionDigits: 4 }),
  }).format(value);
}
