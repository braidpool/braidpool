import { useState } from 'react';
import { RewardsData, BlockData } from './Types';

export function shortenHash(hash: string, start = 6, end = 6): string {
  if (hash.length <= start + end) return hash;
  return `${hash.slice(0, start)}...${hash.slice(-end)}`;
}

export function formatWork(difficulty: number): {
  value: string;
  unit: string;
} {
  const units = ['GH', 'TH', 'PH', 'EH'];
  let work = difficulty / 1e9;
  let i = 0;

  while (work >= 1000 && i < units.length - 1) {
    work /= 1000;
    i++;
  }
  const shouldUseExponential = work >= 1e21;

  return {
    value: shouldUseExponential ? work.toExponential(4) : work.toFixed(2),
    unit: units[i],
  };
}

export function useCopyToClipboard(timeout = 1500) {
  const [copied, setCopied] = useState<string | null>(null);

  const copy = (text: string) => {
    navigator.clipboard.writeText(text).then(() => {
      setCopied(text);
      setTimeout(() => setCopied(null), timeout);
    });
  };

  return { copied, copy };
}

export function processRewardsData(data: RewardsData) {
  const {
    blockCount,
    blockReward,
    totalRewards,
    rewardRate,
    lastRewardTime,
    halvings,
    nextHalving,
    blocksUntilHalving,
  } = data;
  return {
    blockCount,
    blockReward,
    totalRewards: totalRewards,
    rewardRate,
    lastRewardTime: lastRewardTime
      ? new Date(lastRewardTime).toISOString()
      : null,
    unit: 'BTC',
    halvings,
    nextHalving,
    blocksUntilHalving,
  };
}

export function processBlockData(data: BlockData) {
  const {
    blockHash,
    timestamp,
    height,
    difficulty,
    txCount,
    reward,
    parent,
    transactions,
  } = data;

  const work = `${(difficulty / 1e6).toFixed(2)} EH`;
  const formattedTransactions = transactions.map((tx: any) => ({
    ...tx,
    timestamp: new Date(parseInt(tx.timestamp)).toISOString(),
    feePaid: tx.fee.toFixed(8),
  }));
  return {
    blockHash,
    timestamp: new Date(timestamp).toISOString(),
    height,
    work,
    txCount,
    reward,
    parent,
    transactions: formattedTransactions,
  };
}
