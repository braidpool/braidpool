import { TransactionCategory } from './Types';
export { shortenAddress } from '../BitcoinStats/Utils';

/**
 * formats fee to 8 decimal places
 */
export const formatFee = (fee: number): string => {
  return fee.toFixed(8);
};

/**
 * formats fee rate to 1 decimal place
 */
export const formatFeeRate = (feeRate: number): string => {
  return feeRate.toFixed(1);
};

/**
 * formats timestamp to relative time, eg:(2m ago,5h ago..)
 */
export const formatTime = (timestamp?: number): string => {
  if (!timestamp) return '-';
  const now = Date.now() / 1000;
  const diff = now - timestamp;

  if (diff < 60) return 'Just now';
  if (diff < 3600) return `${Math.floor(diff / 60)}m ago`;
  if (diff < 86400) return `${Math.floor(diff / 3600)}h ago`;
  return `${Math.floor(diff / 86400)}d ago`;
};

/**
 * returns Tailwind CSS classes for transaction category badge.
 */

const CATEGORY_STYLE_MAP: {
  [key in TransactionCategory]?: {
    badge: string;
    bordered: string;
  };
} = {
  [TransactionCategory.MEMPOOL]: {
    badge: 'bg-blue-500/20 text-blue-400',
    bordered: 'bg-blue-500/10 border-blue-500/20 text-blue-400',
  },
  [TransactionCategory.COMMITTED]: {
    badge: 'bg-indigo-500/20 text-indigo-400',
    bordered: 'bg-indigo-500/10 border-indigo-500/20 text-indigo-400',
  },
  [TransactionCategory.PROPOSED]: {
    badge: 'bg-green-500/20 text-green-400',
    bordered: 'bg-green-500/10 border-green-500/20 text-green-400',
  },
  [TransactionCategory.SCHEDULED]: {
    badge: 'bg-yellow-500/20 text-yellow-400',
    bordered: 'bg-yellow-500/10 border-yellow-500/20 text-yellow-400',
  },
  [TransactionCategory.CONFIRMED]: {
    badge: 'bg-emerald-500/20 text-emerald-400',
    bordered: 'bg-emerald-500/10 border-emerald-500/20 text-emerald-400',
  },
  [TransactionCategory.REPLACED]: {
    badge: 'bg-red-500/20 text-red-400',
    bordered: 'bg-red-500/10 border-red-500/20 text-red-400',
  },
};
/**
 * returns Tailwind CSS classes for transaction category badge.
 */
export const getCategoryColor = (category: TransactionCategory): string => {
  const styles = CATEGORY_STYLE_MAP[category];
  return styles?.badge ?? 'bg-gray-500/20 text-gray-400';
};
/**
 * returns Tailwind CSS classes for transaction category with border styles.
 */
export const getCategoryStyles = (category: TransactionCategory): string => {
  const styles = CATEGORY_STYLE_MAP[category];
  return styles?.bordered ?? 'bg-gray-500/10 border-gray-500/20 text-gray-400';
};
