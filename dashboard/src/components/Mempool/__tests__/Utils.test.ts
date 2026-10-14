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

  test('keeps sub-unit fees visible', () => {
    expect(formatBtcAmount(0.00000001, 'USD', rates)).toBe('$0.0004');
  });

  test('returns a placeholder when the amount or rate is missing', () => {
    expect(formatBtcAmount(undefined, 'USD', rates)).toBe('--');
    expect(formatBtcAmount(0.5, 'USD', undefined)).toBe('--');
  });
});
