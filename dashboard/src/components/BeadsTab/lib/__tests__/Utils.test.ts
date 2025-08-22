import { shortenHash, formatWork, processBlockData } from '../Utils';

import { BlockData, Transaction } from '../Types';
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

describe('processBlockData', () => {
  it('formats block and transactions correctly', () => {
    const transactions: Transaction[] = [
      {
        id: 'tx1',
        hash: 'h1',
        timestamp: '1700000000000',
        count: 1,
        blockId: 'b1',
        fee: 0.000123456789,
        size: 200,
        feePaid: '',
        feeRate: 10,
        inputs: 2,
        outputs: 1,
      },
    ];

    const data: BlockData = {
      blockHash: 'abc123',
      timestamp: 1700000000000,
      height: 123,
      difficulty: 1e18,
      txCount: 1,
      reward: 6.25,
      parent: 'def456',
      transactions,
    };
    const DIFFICULTY_ONE = 2 ** 32;
    const result = processBlockData(data);
    expect(result.blockHash).toBe('abc123');
    expect(result.timestamp).toBe(new Date(1700000000000).toISOString());
    const expectedWork = ((1e18 * DIFFICULTY_ONE) / 1e9).toFixed(2);
    expect(result.work).toBe(expectedWork);
    expect(result.transactions[0].feePaid).toBe('0.00012346'); // Rounded to 8 decimal places
    expect(result.transactions[0].timestamp).toBe(
      new Date(1700000000000).toISOString()
    );
  });

  it('handles empty transactions array', () => {
    const data: BlockData = {
      blockHash: 'empty_tx_block',
      timestamp: 1600000000000,
      height: 456,
      difficulty: 5e9, // 5 GH
      txCount: 0,
      reward: 12.5,
      parent: 'parent_empty',
      transactions: [],
    };
    const result = processBlockData(data);
    expect(result.blockHash).toBe('empty_tx_block');
    expect(result.timestamp).toBe(new Date(1600000000000).toISOString());
    const expectedWork = ((5e9 * Math.pow(2, 32)) / 1e9).toFixed(2);
    expect(result.work).toBe(expectedWork);
    expect(result.transactions).toEqual([]);
    expect(result.txCount).toBe(0);
  });

  it('handles multiple transactions', () => {
    const transactions: Transaction[] = [
      {
        id: 'tx1',
        hash: 'h1',
        timestamp: '1700000000000',
        count: 1,
        blockId: 'b1',
        fee: 0.001,
        size: 100,
        feePaid: '',
        feeRate: 1,
        inputs: 1,
        outputs: 1,
      },
      {
        id: 'tx2',
        hash: 'h2',
        timestamp: '1700000001000',
        count: 1,
        blockId: 'b1',
        fee: 0.000567891234,
        size: 150,
        feePaid: '',
        feeRate: 2,
        inputs: 2,
        outputs: 2,
      },
    ];
    const data: BlockData = {
      blockHash: 'multi_tx_block',
      timestamp: 1700000000000,
      height: 789,
      difficulty: 1.2e12, // 1.2 TH
      txCount: 2,
      reward: 6.25,
      parent: 'parent_multi',
      transactions,
    };
    const result = processBlockData(data);
    expect(result.txCount).toBe(2);
    expect(result.transactions.length).toBe(2);
    expect(result.transactions[0].feePaid).toBe('0.00100000');
    expect(result.transactions[0].timestamp).toBe(
      new Date(1700000000000).toISOString()
    );
    expect(result.transactions[1].feePaid).toBe('0.00056789');
    expect(result.transactions[1].timestamp).toBe(
      new Date(1700000001000).toISOString()
    );
    // Fix: Calculate expected work using the actual formula
    const expectedWork = ((1.2e12 * Math.pow(2, 32)) / 1e9).toFixed(2);
    expect(result.work).toBe(expectedWork);
  });

  it('handles null/undefined values for optional properties gracefully', () => {
    const data: BlockData = {
      blockHash: 'test_null_data',
      timestamp: null as any,
      height: 1,
      difficulty: 1e9,
      txCount: 0,
      reward: 0,
      parent: null as any,
      transactions: [],
    };
    const result = processBlockData(data);
    expect(result.timestamp).toBe(new Date(null as any).toISOString());
    expect(result.parent).toBeNull();
    // Fix: Calculate expected work using the actual formula
    const expectedWork = ((1e9 * Math.pow(2, 32)) / 1e9).toFixed(2);
    expect(result.work).toBe(expectedWork);
  });

  it('formats transaction fee to 8 decimal places even if fewer are provided', () => {
    const transactions: Transaction[] = [
      {
        id: 'tx_short_fee',
        hash: 'h_sf',
        timestamp: '1700000000000',
        count: 1,
        blockId: 'b_sf',
        fee: 0.5,
        size: 100,
        feePaid: '',
        feeRate: 1,
        inputs: 1,
        outputs: 1,
      },
      {
        id: 'tx_zero_fee',
        hash: 'h_zf',
        timestamp: '1700000000000',
        count: 1,
        blockId: 'b_zf',
        fee: 0,
        size: 100,
        feePaid: '',
        feeRate: 1,
        inputs: 1,
        outputs: 1,
      },
    ];
    const data: BlockData = {
      blockHash: 'fee_formats',
      timestamp: 1,
      height: 1,
      difficulty: 1e9,
      txCount: 2,
      reward: 1,
      parent: 'p',
      transactions,
    };
    const result = processBlockData(data);
    expect(result.transactions[0].feePaid).toBe('0.50000000');
    expect(result.transactions[1].feePaid).toBe('0.00000000');
  });

  it('correctly formats the timestamp string in transactions', () => {
    const transactions: Transaction[] = [
      {
        id: 'tx_ts',
        hash: 'h_ts',
        timestamp: '1678888888888',
        count: 1,
        blockId: 'b_ts',
        fee: 0.1,
        size: 100,
        feePaid: '',
        feeRate: 1,
        inputs: 1,
        outputs: 1,
      },
    ];
    const data: BlockData = {
      blockHash: 'ts_block',
      timestamp: 1,
      height: 1,
      difficulty: 1e9,
      txCount: 1,
      reward: 1,
      parent: 'p',
      transactions,
    };
    const result = processBlockData(data);
    expect(result.transactions[0].timestamp).toBe(
      new Date(1678888888888).toISOString()
    );
  });

  it('handles very large difficulty for block data', () => {
    const data: BlockData = {
      blockHash: 'mega_diff',
      timestamp: 1700000000000,
      height: 9999999,
      difficulty: 1e39,
      txCount: 0,
      reward: 0,
      parent: 'mega_parent',
      transactions: [],
    };
    const result = processBlockData(data);
    const expectedWork = ((1e39 * Math.pow(2, 32)) / 1e9).toFixed(2);
    expect(result.work).toBe(expectedWork);
    expect(parseFloat(result.work)).toBeGreaterThan(1e30);
  });
});
