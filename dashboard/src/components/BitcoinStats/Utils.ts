import axios from 'axios';
import { useState } from 'react';
import {
  getMempoolRecentUrl,
  getMempoolTransactionUrl,
  getBraidPoolReplacementsUrl,
} from '../../URLs';
import { TransactionCategory } from "./Types";


export const getCurrencySymbol = (curr: string) => {
  switch (curr) {
    case 'EUR':
      return '€';
    case 'GBP':
      return '£';
    case 'JPY':
      return '¥';
    default:
      return '$';
  }
};

export const formatPrice = (value: number): string => {
  if (!value) return '--';
  return new Intl.NumberFormat('en-US', {
    minimumFractionDigits: 2,
    maximumFractionDigits: 2,
  }).format(value);
};

export const formatLargeNumber = (value: number): string => {
  if (!value) return '--';
  if (value >= 1e12) return `${(value / 1e12).toFixed(2)}T`;
  if (value >= 1e9) return `${(value / 1e9).toFixed(2)}B`;
  if (value >= 1e6) return `${(value / 1e6).toFixed(2)}M`;
  return new Intl.NumberFormat('en-US').format(value);
};

export const shortenAddress = (value: string): string => {
  if (!value) return 'N/A';
  else if (value.length < 15) return value;
  return value.slice(0, 7) + '....' + value.slice(-7);
};

// via esplora
export const getLatestTransactions = async (): Promise<any> => {
  try {
    const response = await axios.get(getMempoolRecentUrl());
    console.log(response.data);
    return response.data;
  } catch (error) {
    console.error('Error fetching transactions:', error);
    throw error;
  }
};

// via esplora
export const getTxInfo = async (txid: string): Promise<any> => {
  try {
    const response = await axios.get(getMempoolTransactionUrl(txid));
    console.log(response.data);
    return response.data;
  } catch (error) {
    console.error('Error fetching transactions:', error);
    throw error;
  }
};

// via mempool api
export const latestRBFTransactions = async (): Promise<any> => {
  try {
    const response = await axios.get(getBraidPoolReplacementsUrl());
    console.log(response.data);
    return response.data;
  } catch (error) {
    console.error('Error fetching RBF Transactions:', error);
    throw error;
  }
};

export const useCopyToClipboard = (
  timeout: number = 1500
): [boolean, (text: string) => void] => {
  const [copied, setCopied] = useState(false);

  const copy = (text: string) => {
    if (!navigator?.clipboard) return;
    navigator.clipboard.writeText(text);
    setCopied(true);
    setTimeout(() => setCopied(false), timeout);
  };

  return [copied, copy];
};


/**
 * truncates a transaction hash to show first 8 and last 8 characters
 */
export const truncateHash = (hash: string): string => {
  if (!hash) return "N/A";
  return hash.substring(0, 8) + "..." + hash.substring(hash.length - 8);
};

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
  if (!timestamp) return "-";
  const now = Date.now() / 1000;
  const diff = now - timestamp;

  if (diff < 60) return "Just now";
  if (diff < 3600) return `${Math.floor(diff / 60)}m ago`;
  if (diff < 86400) return `${Math.floor(diff / 3600)}h ago`;
  return `${Math.floor(diff / 86400)}d ago`;
};

/**
 * returns Tailwind CSS classes for transaction category badge.
 */
export const getCategoryColor = (category: TransactionCategory): string => {
  switch (category) {
    case TransactionCategory.MEMPOOL:
      return "bg-blue-500/20 text-blue-400";
    case TransactionCategory.COMMITTED:
      return "bg-indigo-500/20 text-indigo-400";
    case TransactionCategory.PROPOSED:
      return "bg-green-500/20 text-green-400";
    case TransactionCategory.SCHEDULED:
      return "bg-yellow-500/20 text-yellow-400";
    case TransactionCategory.CONFIRMED:
      return "bg-emerald-500/20 text-emerald-400";
    case TransactionCategory.REPLACED:
      return "bg-red-500/20 text-red-400";
    default:
      return "bg-gray-500/20 text-gray-400";
  }
};

/**
 * returns Tailwind CSS classes for transaction category with border styles.
 */
export const getCategoryStyles = (category: TransactionCategory): string => {
  const styles = {
    [TransactionCategory.MEMPOOL]:
      "bg-blue-500/10 border-blue-500/20 text-blue-400",
    [TransactionCategory.COMMITTED]:
      "bg-indigo-500/10 border-indigo-500/20 text-indigo-400",
    [TransactionCategory.PROPOSED]:
      "bg-green-500/10 border-green-500/20 text-green-400",
    [TransactionCategory.SCHEDULED]:
      "bg-yellow-500/10 border-yellow-500/20 text-yellow-400",
    [TransactionCategory.CONFIRMED]:
      "bg-emerald-500/10 border-emerald-500/20 text-emerald-400",
    [TransactionCategory.REPLACED]:
      "bg-red-500/10 border-red-500/20 text-red-400",
  };
  return styles[category] || "bg-gray-500/10 border-gray-500/20 text-gray-400";
};

