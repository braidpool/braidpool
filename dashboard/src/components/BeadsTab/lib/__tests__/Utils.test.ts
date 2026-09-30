import { shortenHash, formatWork } from '../Utils';

import { describe, it, expect } from '@jest/globals';

describe('shortenHash', () => {
  it('shortens a long hash correctly', () => {
    const result = shortenHash('abcdef1234567890abcdef');
    expect(result).toBe('abcdef...abcdef');
  });

  it('returns hash as-is if it is short', () => {
    const result = shortenHash('abc123', 3, 3);
    expect(result).toBe('abc123');
  });

  it('handles empty string input', () => {
    const result = shortenHash('');
    expect(result).toBe('');
  });

  it('shortens a hash with custom lengths', () => {
    const result = shortenHash('abcdef1234567890abcdef', 4, 4);
    expect(result).toBe('abcd...cdef');
  });

  it('shortens a hash when start length is greater than end length', () => {
    const result = shortenHash('abcdefghijklmnopqrstuvwxyz', 8, 4);
    expect(result).toBe('abcdefgh...wxyz');
  });
});

describe('formatWork', () => {
  it('formats difficulty into GH', () => {
    const result = formatWork(10e9); // 10 GH
    expect(result).toEqual({ value: '10.00', unit: 'GH' });
  });

  it('formats very large difficulty into EH', () => {
    const result = formatWork(1e18); // 1 EH
    expect(result).toEqual({ value: '1.00', unit: 'EH' });
  });

  it('shows exponential notation for just above values', () => {
    const result = formatWork(1e21 + 1);
    expect(result.value).toBe('1000.00');
    expect(result.unit).toBe('EH');
  });

  it('shows exponential notation for very high values', () => {
    const result = formatWork(1e50);
    expect(result.value).toMatch(/e\+/); // exponential
    expect(result.unit).toBe('EH'); // It should be the largest unit
  });

  it('formats difficulty less than 1 GH', () => {
    const result = formatWork(5e8); // 0.5 GH
    expect(result).toEqual({ value: '0.50', unit: 'GH' });
  });

  it('formats difficulty exactly 1 GH', () => {
    const result = formatWork(1e9); // 1 GH
    expect(result).toEqual({ value: '1.00', unit: 'GH' });
  });

  it('formats difficulty for TH (thousands of GH)', () => {
    const result = formatWork(1.5e12); // 1500 GH = 1.5 TH
    expect(result).toEqual({ value: '1.50', unit: 'TH' });
  });

  it('formats difficulty for PH (thousands of TH)', () => {
    const result = formatWork(2.5e15); // 2500 TH = 2.5 PH
    expect(result).toEqual({ value: '2.50', unit: 'PH' });
  });

  it('formats difficulty for EH (thousands of PH)', () => {
    const result = formatWork(3.75e18); // 3750 PH = 3.75 EH
    expect(result).toEqual({ value: '3.75', unit: 'EH' });
  });

  it('handles zero difficulty', () => {
    const result = formatWork(0);
    expect(result).toEqual({ value: '0.00', unit: 'GH' });
  });

  it('handles negative difficulty (though unlikely but sometimes server has shown this in logs so shall be handled)', () => {
    const result = formatWork(-10e9); // -10 GH
    expect(result).toEqual({ value: '-10.00', unit: 'GH' });
  });

  it('formats a value that is exactly 999.999... before rounding', () => {
    const result = formatWork(999.999e9); // 999.999 GH -> rounds to 1000.00 GH but unit should stay GH
    expect(result).toEqual({ value: '1000.00', unit: 'GH' });
  });

  it('formats a value that crosses unit threshold exactly', () => {
    const result = formatWork(1000e9); // 1000 GH = 1 TH
    expect(result).toEqual({ value: '1.00', unit: 'TH' });
  });

  it('correctly handles extremely large values', () => {
    const result = formatWork(1e39);
    expect(result.value).toMatch(/(\d+(\.\d+)?(e\+\d+)?)/);
    expect(result.unit).toBe('EH');
  });

  it('correctly handles values that are just below the exponential threshold', () => {
    const valueJustBelowExponential = 9.9999e28;
    const result = formatWork(valueJustBelowExponential);
    expect(result.value).not.toMatch(/e\+/); // Should not be exponential
    expect(result.unit).toBe('EH');
  });
});
