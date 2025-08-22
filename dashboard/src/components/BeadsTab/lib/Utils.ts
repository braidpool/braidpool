import { useState } from 'react';
import { BlockData, RewardPoint } from './Types';

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
  const DIFFICULTY_ONE = 2 ** 32;
  const workInGH = ((difficulty * DIFFICULTY_ONE) / 1e9).toFixed(2);
  const formattedTransactions = transactions.map((tx: any) => ({
    ...tx,
    timestamp: new Date(parseInt(tx.timestamp)).toISOString(),
    feePaid: tx.fee.toFixed(8),
  }));
  return {
    blockHash,
    timestamp: new Date(timestamp).toISOString(),
    height,
    work: workInGH,
    txCount,
    reward,
    parent,
    transactions: formattedTransactions,
  };
}
export function calculateRewardAnalytics(rewardHistory: RewardPoint[]) {
  if (!rewardHistory || rewardHistory.length === 0) {
    return {
      avgBTC: 0,
      avgUSD: 0,
      rewardsPerHour: { BTC: 0, USD: 0, blocks: 0 },
      rewardsPerWeek: { BTC: 0, USD: 0, blocks: 0 },
      rewardsPerMonth: { BTC: 0, USD: 0, blocks: 0 },
    };
  }

  const totalBTC = rewardHistory.reduce((sum, r) => sum + r.rewardBTC, 0);
  const totalUSD = rewardHistory.reduce((sum, r) => sum + r.rewardUSD, 0);
  const avgBTC = totalBTC / rewardHistory.length;
  const avgUSD = totalUSD / rewardHistory.length;

  const now = new Date();
  const oneHourAgo = new Date(now.getTime() - 60 * 60 * 1000);
  const oneWeekAgo = new Date(now.getTime() - 7 * 24 * 60 * 60 * 1000);
  const oneMonthAgo = new Date(now.getTime() - 30 * 24 * 60 * 60 * 1000);

  const parseTimestamp = (timestamp: string) => new Date(timestamp);

  const blocksLastHour = rewardHistory.filter(
    (r) => parseTimestamp(r.timestamp) >= oneHourAgo
  );
  const blocksLastWeek = rewardHistory.filter(
    (r) => parseTimestamp(r.timestamp) >= oneWeekAgo
  );
  const blocksLastMonth = rewardHistory.filter(
    (r) => parseTimestamp(r.timestamp) >= oneMonthAgo
  );

  return {
    avgBTC: parseFloat(avgBTC.toFixed(8)),
    avgUSD: parseFloat(avgUSD.toFixed(2)),
    rewardsPerHour: {
      BTC: blocksLastHour.reduce((sum, r) => sum + r.rewardBTC, 0),
      USD: blocksLastHour.reduce((sum, r) => sum + r.rewardUSD, 0),
      blocks: blocksLastHour.length,
    },
    rewardsPerWeek: {
      BTC: blocksLastWeek.reduce((sum, r) => sum + r.rewardBTC, 0),
      USD: blocksLastWeek.reduce((sum, r) => sum + r.rewardUSD, 0),
      blocks: blocksLastWeek.length,
    },
    rewardsPerMonth: {
      BTC: blocksLastMonth.reduce((sum, r) => sum + r.rewardBTC, 0),
      USD: blocksLastMonth.reduce((sum, r) => sum + r.rewardUSD, 0),
      blocks: blocksLastMonth.length,
    },
  };
}

export function formatValue(value: number, type: 'BTC' | 'USD'): string {
  if (type === 'BTC') {
    return value.toFixed(2);
  } else {
    return value.toLocaleString('en-US', {
      minimumFractionDigits: 2,
      maximumFractionDigits: 2,
    });
  }
}
export function formatFeePercentage(fees: string | number): string {
  const value = parseFloat(String(fees)) * 100;
  return `${Math.abs(value).toFixed(2)}%`;
}
