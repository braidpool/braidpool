import { formatBtcAmount } from '../Utils';

const rates = { USD: 37000, EUR: 34500, JPY: 4000000 };

describe('formatBtcAmount', () => {
  test('formats BTC to 8 decimals', () => {
    expect(formatBtcAmount(0.5, 'BTC', rates)).toBe('0.50000000 BTC');
  });

  test('converts to fiat with the currency symbol and precision', () => {
    expect(formatBtcAmount(1.23456789, 'USD', rates)).toBe('$45,679.01');
    expect(formatBtcAmount(1.23456789, 'EUR', rates)).toBe('€42,592.59');
    expect(formatBtcAmount(1.23456789, 'JPY', rates)).toBe('¥4,938,272');
  });

  test('keeps per-vbyte fees precise', () => {
    expect(formatBtcAmount(0.00000001, 'USD', rates)).toBe('$0.0004');
    expect(formatBtcAmount(0.00012345, 'USD', rates)).toBe('$4.5676');
    expect(formatBtcAmount(0.00000029, 'JPY', { ...rates, JPY: 6500000 })).toBe(
      '¥1.885'
    );
  });

  test('formats BTC without rates', () => {
    expect(formatBtcAmount(0.5, 'BTC', undefined)).toBe('0.50000000 BTC');
  });

  test('returns a placeholder when the amount or rate is missing', () => {
    expect(formatBtcAmount(undefined, 'USD', rates)).toBe('--');
    expect(formatBtcAmount(NaN, 'USD', rates)).toBe('--');
    expect(formatBtcAmount(0.5, 'USD', undefined)).toBe('--');
    expect(formatBtcAmount(0.5, 'USD', { ...rates, USD: 0 })).toBe('--');
  });
});
