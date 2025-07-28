import { generateRewardHistory } from '../generateRewardHistory';
import { describe, test, expect } from '@jest/globals';

describe('generateRewardHistory', () => {
  test('should generate a history for a small block count (less than 1000)', () => {
    const blockCount = 500;
    const history = generateRewardHistory(blockCount);

    expect(history[0].height).toBe(0);
    expect(history[history.length - 1].height).toBe(blockCount);

    expect(history[0].reward).toBe(50);
    expect(history.every((item) => item.reward === 50)).toBe(true);
    expect(history.length).toBeGreaterThan(1);
    expect(history.length).toBe(51); // (500 - 0) / 10 + 1
  });

  test('should return an array with a single item for blockCount 0', () => {
    const blockCount = 0;
    const history = generateRewardHistory(blockCount);

    expect(history.length).toBe(1);
    expect(history[0]).toEqual({ height: 0, reward: 50, label: 'Block 0' });
  });

  test('should return an array with two items for blockCount 1', () => {
    const blockCount = 1;
    const history = generateRewardHistory(blockCount);

    expect(history.length).toBe(2);
    expect(history[0]).toEqual({ height: 0, reward: 50, label: 'Block 0' });
    expect(history[1]).toEqual({ height: 1, reward: 50, label: 'Block 1' });
  });

  test('should generate history for the last 1000 blocks when blockCount is large but before first halving', () => {
    const blockCount = 200000;
    const history = generateRewardHistory(blockCount);
    const maxBlocks = 1000;

    expect(history[0].height).toBe(blockCount - maxBlocks); // 199000
    expect(history[history.length - 1].height).toBe(blockCount); // 200000

    const expectedStep = Math.max(1, Math.floor(maxBlocks / 50)); // 20
    expect(expectedStep).toBe(20);
    expect(history.length).toBe(51); // (1000 / 20) + 1

    // All rewards should still be 50 as its before the first halving
    expect(history.every((item) => item.reward === 50)).toBe(true);
  });

  test('should correctly calculate rewards around the first halving event (exact points)', () => {
    const blockCountBeforeHalving = 209999;
    const historyBefore = generateRewardHistory(blockCountBeforeHalving);
    expect(historyBefore[historyBefore.length - 1].height).toBe(209999);
    expect(historyBefore[historyBefore.length - 1].reward).toBe(50);

    const blockCountAtHalving = 210000;
    const historyAt = generateRewardHistory(blockCountAtHalving);
    const block210000At = historyAt.find((item) => item.height === 210000);
    expect(block210000At?.reward).toBe(25);

    const blockCountAfterHalving = 210001;
    const historyAfter = generateRewardHistory(blockCountAfterHalving);
    const block210001After = historyAfter.find(
      (item) => item.height === 210001
    );
    expect(block210001After?.reward).toBe(25);
  });

  test('should correctly calculate rewards when history spans the first halving event', () => {
    const blockCount = 210500;
    const history = generateRewardHistory(blockCount);

    expect(history[0].height).toBe(blockCount - 1000); // Should start at 209500
    expect(history[history.length - 1].height).toBe(blockCount); // Should end at 210500
    expect(history.length).toBe(51); // (1000 / 20) + 1

    // Verify rewards for blocks before, at, and after the halving within this window
    const block209500 = history.find((item) => item.height === 209500);
    expect(block209500?.reward).toBe(50); // Before halving

    const block210000 = history.find((item) => item.height === 210000);
    expect(block210000?.reward).toBe(25); // At halving

    const block210500 = history.find((item) => item.height === 210500);
    expect(block210500?.reward).toBe(25); // After halving
  });

  test('should correctly calculate rewards around the second halving event (exact points)', () => {
    const blockCountBeforeSecondHalving = 419999;
    const historyBefore = generateRewardHistory(blockCountBeforeSecondHalving);
    expect(historyBefore[historyBefore.length - 1].height).toBe(419999);
    expect(historyBefore[historyBefore.length - 1].reward).toBe(25);

    const blockCountAtSecondHalving = 420000;
    const historyAt = generateRewardHistory(blockCountAtSecondHalving);
    const block420000At = historyAt.find((item) => item.height === 420000);
    expect(block420000At?.reward).toBe(12.5);

    const blockCountAfterSecondHalving = 420001;
    const historyAfter = generateRewardHistory(blockCountAfterSecondHalving);
    const block420001After = historyAfter.find(
      (item) => item.height === 420001
    );
    expect(block420001After?.reward).toBe(12.5);
  });

  test('should correctly calculate rewards when history spans the second halving event', () => {
    const blockCount = 420500; // Current block is after the second halving
    const history = generateRewardHistory(blockCount);

    expect(history[0].height).toBe(blockCount - 1000); // Should start at 419500
    expect(history[history.length - 1].height).toBe(blockCount); // Should end at 420500
    expect(history.length).toBe(51); // (1000 / 20) + 1

    // Verify rewards for blocks before, at, and after the halving within this window
    const block419500 = history.find((item) => item.height === 419500);
    expect(block419500?.reward).toBe(25); // Before halving

    const block420000 = history.find((item) => item.height === 420000);
    expect(block420000?.reward).toBe(12.5); // At halving

    const block420500 = history.find((item) => item.height === 420500);
    expect(block420500?.reward).toBe(12.5); // After halving
  });

  test('should use a step size of 1 when maxBlocks is small (blockCount < 50)', () => {
    const blockCount = 40; // maxBlocks will be 40
    const history = generateRewardHistory(blockCount);
    expect(history[1].height - history[0].height).toBe(1);
    expect(history.length).toBe(blockCount + 1); // From 0 to 40, step 1
  });

  test('should use a step size of 20 when maxBlocks is 1000 (blockCount >= 1000)', () => {
    const blockCount = 1000; // maxBlocks will be 1000
    const history = generateRewardHistory(blockCount);
    expect(history[1].height - history[0].height).toBe(20);
    expect(history.length).toBe(51); // (1000 - 0) / 20 + 1
  });

  test('should use a step size of 10 when blockCount is 500 (maxBlocks = 500)', () => {
    const blockCount = 500; // maxBlocks will be 500
    const history = generateRewardHistory(blockCount);
    expect(history[1].height - history[0].height).toBe(10);
    expect(history.length).toBe(51); // (500 - 0) / 10 + 1
  });

  test('should have correctly formatted labels', () => {
    const blockCount = 50;
    const history = generateRewardHistory(blockCount);
    expect(history[0].label).toBe('Block 0');
    expect(history[history.length - 1].label).toBe('Block 50');
  });

  test('should return items with height, reward, and label properties', () => {
    const blockCount = 100;
    const history = generateRewardHistory(blockCount);
    history.forEach((item) => {
      expect(item).toHaveProperty('height');
      expect(item).toHaveProperty('reward');
      expect(item).toHaveProperty('label');
      expect(typeof item.height).toBe('number');
      expect(typeof item.reward).toBe('number');
      expect(typeof item.label).toBe('string');
    });
  });
});
