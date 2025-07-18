import axios from 'axios';
import { useState } from 'react';

// via mempool api
export const getBlockInfo = async (hash: string): Promise<any> => {
  try {
    const response = await axios.get(
      `http://localhost:8999/api/v1/block/${hash}`
    );
    console.log(response.data);
    return response.data;
  } catch (error) {
    console.error('Error fetching block info:', error);
    throw error;
  }
};

export const fetchPreviousBlocks = async () => {
  try {
    const response = await fetch('http://localhost:8999/api/v1/blocks');
    if (!response.ok) throw new Error('Network response was not ok');
    const data = await response.json();
    return data;
  } catch (err) {
    console.error('Failed to fetch previous blocks', err);
    throw err;
  }
};

export function formatUnixTimestamp(timestamp: number): string {
  const date = new Date(timestamp * 1000);
  return date.toTimeString().slice(0, 8); // "HH:MM:SS"
}

export const formatTimestamp = (ts: number) => {
  const d = new Date(ts * 1000);
  return d.toLocaleString();
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
