import {
  HistoryEntry,
  LatencyEntry,
  ProcessedHashrateData,
  ProcessedLatencyData,
  BlockData,
  RewardsData,
} from '../types';

const MAX_HISTORY_LENGTH = 288;
const MAX_LATENCY_HISTORY = 100;

let hashrateHistory: HistoryEntry[] = [];
let latencyHistory: LatencyEntry[] = [];
let peakHashrate = 0;

export function processHashrateData(data: ProcessedHashrateData) {
  const { hashrate, timestamp, networkDifficulty, latency } = data;

  const historyEntry = {
    value: hashrate,
    date: new Date(timestamp).toISOString(),
    label: new Date(timestamp).toLocaleTimeString(),
    timestamp: new Date(timestamp).getTime(),
  };

  if (hashrateHistory.length >= MAX_HISTORY_LENGTH) {
    hashrateHistory.shift();
  }
  hashrateHistory.push(historyEntry);

  if (hashrate > peakHashrate) {
    peakHashrate = hashrate;
  }

  return {
    history: hashrateHistory,
    current: `${hashrate.toFixed(2)} EH/s`,
    peak: `${peakHashrate.toFixed(2)} EH/s`,
    networkDifficulty,
    latency,
  };
}

export function processLatencyData(data: ProcessedLatencyData) {
  const {
    pings,
    averageLatency,
    peakLatency,
    peerCount,
    validPings,
    timestamp,
  } = data;

  if (pings.length === 0) {
    return {
      chartData: latencyHistory,
      averageLatency: '0ms',
      peakLatency: '0ms',
      peerCount,
      totalPeers: peerCount,
      validPings: 0,
      timestamp,
    };
  }

  const newEntry = {
    value: averageLatency,
    label: new Date(timestamp).toLocaleTimeString(),
    date: new Date(timestamp).toISOString(),
    timeStamp: new Date(timestamp).toISOString(),
  };
  latencyHistory.push(newEntry);

  while (latencyHistory.length > MAX_LATENCY_HISTORY) {
    latencyHistory.shift();
  }

  return {
    chartData: latencyHistory,
    averageLatency: `${averageLatency.toFixed(0)}ms`,
    peakLatency: `${peakLatency}ms`,
    peerCount,
    totalPeers: peerCount,
    validPings,
    timestamp,
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
    timestamp: new Date(tx.timestamp).toISOString(),
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

export function formatTimestamp(timestamp: number): string {
  return new Date(timestamp).toISOString();
}

export function formatTimeLabel(timestamp: number): string {
  return new Date(timestamp).toLocaleTimeString();
}

export function clearHistory() {
  hashrateHistory = [];
  latencyHistory = [];
  peakHashrate = 0;
}
