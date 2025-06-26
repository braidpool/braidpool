import { BlockData } from '../types';

export function processBlockData(data: BlockData) {
  const { blockHash, timestamp, height, difficulty, txCount, reward, parent, transactions } = data;
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