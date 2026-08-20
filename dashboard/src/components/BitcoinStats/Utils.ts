import axios from 'axios';
import { useState } from 'react';
import {
  getBraidpoolNodeRpcUrl,
} from '../../URLs';

const RPC_TIMEOUT = 8000;
let _rpcId = 0;
const nextId = () => ++_rpcId;

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

const _upliftCache = new Map<string, 'mined' | 'confirmed'>();
const _noUpliftCount = new Map<string, number>();
const NO_UPLIFT_GIVE_UP = 3; 

export const getLatestTransactions = async (): Promise<any> => {
  const [mempoolResult, stagedResult, committedResult] = await Promise.allSettled([
    axios.post(
      getBraidpoolNodeRpcUrl(),
      { jsonrpc: '2.0', id: nextId(), method: 'getmempoolentries', params: [20] },
      { timeout: RPC_TIMEOUT }
    ),
    axios.post(
      getBraidpoolNodeRpcUrl(),
      { jsonrpc: '2.0', id: nextId(), method: 'stagedtransactions', params: [] },
      { timeout: RPC_TIMEOUT }
    ),
    axios.post(
      getBraidpoolNodeRpcUrl(),
      { jsonrpc: '2.0', id: nextId(), method: 'getcommittedtransactions', params: [0, 20] },
      { timeout: RPC_TIMEOUT }
    ),
  ]);

  const txMap = new Map<string, any>();
  if (committedResult.status === 'fulfilled' && !committedResult.value.data.error) {
    const entries: any[] = committedResult.value.data.result?.transactions ?? [];
    for (const tx of entries) {
      txMap.set(tx.txid, {
        txid: tx.txid,
        fee: 0,
        vsize: 0,
        value: 0,
        time: tx.timestamp,
        stage: 'committed',
      });
    }
  }
  if (stagedResult.status === 'fulfilled' && !stagedResult.value.data.error) {
    const entries: any[] = stagedResult.value.data.result ?? [];
    for (const entry of entries) {
      if (!txMap.has(entry.txid)) {
        const totalValue = (entry.tx?.output ?? []).reduce(
          (sum: number, out: any) => sum + (out.value ?? 0),
          0
        );
        txMap.set(entry.txid, {
          txid: entry.txid,
          fee: 0,
          vsize: 0,
          value: totalValue,
          time: 0,
          stage: 'staged',
        });
      }
    }
  }
  if (mempoolResult.status === 'fulfilled' && !mempoolResult.value.data.error) {
    const entries: any[] = mempoolResult.value.data.result ?? [];
    for (const tx of entries) {
      if (!txMap.has(tx.txid)) {
        txMap.set(tx.txid, {
          txid: tx.txid,
          fee: tx.fee,
          vsize: tx.vsize,
          value: 0,
          time: tx.time,
          stage: 'mempool',
        });
      }
    }
  }

  if (txMap.size === 0) {
    throw new Error('Unable to fetch transactions: node unreachable or all RPCs failed');
  }
  const committedTxids = Array.from(txMap.values())
    .filter((tx) => tx.stage === 'committed')
    .map((tx) => tx.txid as string);
  for (const txid of committedTxids) {
    const cached = _upliftCache.get(txid);
    if (cached) {
      const tx = txMap.get(txid);
      if (tx) tx.stage = cached;
    }
  }
  const uncachedTxids = committedTxids.filter(
    (txid) => !_upliftCache.has(txid) && (_noUpliftCount.get(txid) ?? 0) < NO_UPLIFT_GIVE_UP
  );

  if (uncachedTxids.length > 0) {
    const statusResults = await Promise.allSettled(
      uncachedTxids.map((txid) =>
        axios.post(
          getBraidpoolNodeRpcUrl(),
          { jsonrpc: '2.0', id: nextId(), method: 'gettransactionstatus', params: [txid] },
          { timeout: RPC_TIMEOUT }
        )
      )
    );
    statusResults.forEach((result, i) => {
      const txid = uncachedTxids[i];
      if (result.status === 'fulfilled' && !result.value.data.error) {
        const stageName: string = result.value.data.result?.stage_name;
        if (stageName === 'mined' || stageName === 'confirmed') {
          _upliftCache.set(txid, stageName);
          const tx = txMap.get(txid);
          if (tx) tx.stage = stageName;
        } else {
          _noUpliftCount.set(txid, (_noUpliftCount.get(txid) ?? 0) + 1);
        }
      } else {
        _noUpliftCount.set(txid, (_noUpliftCount.get(txid) ?? 0) + 1);
      }
    });
  }
  const stageOrder: Record<string, number> = {
    confirmed: 0,
    mined:     1,
    committed: 2,
    staged:    3,
    mempool:   4,
  };
  return Array.from(txMap.values()).sort((a, b) => {
    const so = (stageOrder[a.stage] ?? 9) - (stageOrder[b.stage] ?? 9);
    if (so !== 0) return so;
    return (b.time ?? 0) - (a.time ?? 0);
  });
};


export const getTxInfo = async (txid: string): Promise<any> => {
  try {
    const response = await axios.post(
      getBraidpoolNodeRpcUrl(),
      { jsonrpc: '2.0', id: nextId(), method: 'gettransactionstatus', params: [txid] },
      { timeout: RPC_TIMEOUT }
    );
    if (response.data.error) {
      throw new Error(response.data.error.message ?? 'RPC error from gettransactionstatus');
    }
    const result = response.data.result;
    if (!result) throw new Error('Empty result from gettransactionstatus');
    const { stage_name, detail = {} } = result;
    const feeSats =
      detail.fee != null ? Math.round(Math.abs(detail.fee) * 1e8) : null;
    return {
      txid: result.txid,
      stage: stage_name,
      bead_hash: detail.bead_hash ?? null,
      status: {
        confirmed: stage_name === 'mined' || stage_name === 'confirmed',
      },
      fee: feeSats,
      size: detail.size ?? null,
      vsize: detail.vsize ?? null,
      weight: detail.weight ?? null,
      version: detail.version ?? null,
      locktime: detail.locktime ?? null,
      vin: (detail.vin ?? []).map((input: any) => ({
        txid: input.txid,
        vout: input.vout,
        prevout: null,
      })),
      vout: (detail.vout ?? []).map((out: any) => ({
        scriptpubkey_address:
          out.scriptPubKey?.address ??
          out.scriptPubKey?.addresses?.[0] ??
          null,
        value: Math.round((out.value ?? 0) * 1e8),
      })),
    };
  } catch (error) {
    console.error('Error fetching transaction info:', error);
    throw error;
  }
};

export const latestRBFTransactions = async (): Promise<any[]> => {
  const response = await axios.post(
    getBraidpoolNodeRpcUrl(),
    { jsonrpc: '2.0', id: nextId(), method: 'getmempoolentries', params: [200] },
    { timeout: RPC_TIMEOUT }
  );
  if (response.data.error) {
    throw new Error(response.data.error.message ?? 'getmempoolentries RPC error');
  }
  const entries: any[] = response.data.result ?? [];
  return entries
    .filter((tx) => tx.rbf === true)
    .sort((a, b) => (b.fee_rate ?? 0) - (a.fee_rate ?? 0))
    .map((tx) => ({
      tx: {
        txid: tx.txid,
        fee: tx.fee ?? 0,
        vsize: tx.vsize ?? 0,
        value: 0,
        rate: tx.fee_rate ?? 0,
        rbf: true,
      },
      time: tx.time ?? 0,
      replaces: [],
    }));
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
