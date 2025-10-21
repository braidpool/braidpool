import { describe, it, expect } from 'vitest';
import {
  TransactionCategory,
  TRANSACTION_CATEGORY_LABELS,
  TRANSACTION_CATEGORY_DESCRIPTIONS,
} from '../transaction';

describe('Transaction Types - Basic Tests', () => {
  describe('TransactionCategory Enum', () => {
    it('has correct enum values', () => {
      expect(TransactionCategory.MEMPOOL).toBe('mempool');
      expect(TransactionCategory.COMMITTED).toBe('committed');
      expect(TransactionCategory.CONFIRMED).toBe('confirmed');
    });

    it('has 6 categories', () => {
      const categories = Object.values(TransactionCategory);
      expect(categories).toHaveLength(6);
    });
  });

  describe('Category Labels', () => {
    it('has labels for all categories', () => {
      expect(TRANSACTION_CATEGORY_LABELS[TransactionCategory.MEMPOOL]).toBe(
        'Mempool'
      );
      expect(TRANSACTION_CATEGORY_LABELS[TransactionCategory.CONFIRMED]).toBe(
        'Confirmed'
      );
    });

    it('has correct number of labels', () => {
      const labels = Object.keys(TRANSACTION_CATEGORY_LABELS);
      expect(labels.length).toBe(6);
    });
  });

  describe('Category Descriptions', () => {
    it('has descriptions for all categories', () => {
      expect(
        TRANSACTION_CATEGORY_DESCRIPTIONS[TransactionCategory.MEMPOOL]
      ).toContain('mempool');
      expect(
        TRANSACTION_CATEGORY_DESCRIPTIONS[TransactionCategory.CONFIRMED]
      ).toContain('confirmed');
    });

    it('all descriptions are non-empty', () => {
      Object.values(TRANSACTION_CATEGORY_DESCRIPTIONS).forEach((desc) => {
        expect(desc.length).toBeGreaterThan(0);
      });
    });
  });
});
