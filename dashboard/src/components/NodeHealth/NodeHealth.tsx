import React, { useState, useEffect, useRef } from 'react';
import Peers from './Peers';
import NetworkPanel from './Network';
import MempoolPanel from './Mempool';
import BandwidthPanel from './Bandwidth';
import { InfoRow } from './InfoRow';
import { TABS, useIsSmallScreen } from './Utils';
import { shortenHash, useCopyToClipboard } from '../BeadsTab/lib/Utils';
import { WEBSOCKET_URLS } from '../../URLs';
import { MAX_RECONNECT_ATTEMPTS } from './Constants';
import {
  Loader,
  Clock,
  CheckCircle2,
  Box,
  Users,
  Layers,
  Link2,
  Copy,
  Check,
} from 'lucide-react';

import {
  BlockchainInfo,
  PeerInfo,
  NetworkInfo,
  MempoolInfo,
  NetTotals,
  BandwidthHistoryPoint,
} from './Types';

const NodeHealth: React.FC = () => {
  const [activeTab, setActiveTab] = useState('blockchain');
  const [blockchainInfo, setBlockchainInfo] = useState<BlockchainInfo | null>(
    null
  );
  const [peerInfo, setPeerInfo] = useState<PeerInfo[]>([]);
  const [networkInfo, setNetworkInfo] = useState<NetworkInfo | null>(null);
  const [mempoolInfo, setMempoolInfo] = useState<MempoolInfo | null>(null);
  const [netTotals, setNetTotals] = useState<NetTotals | null>(null);
  const [lastUpdated, setLastUpdated] = useState<string>('');
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);
  const [wsConnected, setWsConnected] = useState(false);
  const [bandwidthHistory, setBandwidthHistory] = useState<
    BandwidthHistoryPoint[]
  >([]);

  const wsRef = useRef<WebSocket | null>(null);
  const reconnectTimeoutRef = useRef<NodeJS.Timeout | null>(null);
  const isSmallScreen = useIsSmallScreen();
  const { copied, copy } = useCopyToClipboard();

  useEffect(() => {
    let isMounted = true;
    let reconnectAttempts = 0;
    const maxReconnectAttempts = MAX_RECONNECT_ATTEMPTS;

    const connect = () => {
      const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
      wsRef.current = ws;

      ws.onopen = () => {
        if (!isMounted) return;
        setWsConnected(true);
        reconnectAttempts = 0;
      };

      ws.onerror = (err: Event) => {
        if (!isMounted) return;
        setWsConnected(false);
        if (process.env.NODE_ENV !== 'test') {
          console.error('WebSocket error:', err);
        }
        setLoading(false);
        setError('WebSocket connection failed');
      };

      ws.onmessage = (event) => {
        if (!isMounted) return;
        try {
          const message = JSON.parse(event.data);
          if (message.type === 'node_health_data') {
            const data = message.data;
            setBlockchainInfo(data.blockchainInfo);
            setPeerInfo(data.peerInfo);
            setNetworkInfo(data.networkInfo);
            setMempoolInfo(data.mempoolInfo);
            setNetTotals(data.netTotals);
            setLastUpdated(new Date(data.lastUpdated).toLocaleTimeString());
            setLoading(false);
            setError(null);
            setBandwidthHistory((prevHistory) => {
              const timestamp = new Date(data.lastUpdated).getTime();
              const { totalbytesrecv, totalbytessent } = data.netTotals;

              if (prevHistory.length === 0) {
                return [
                  {
                    timestamp,
                    totalbytesrecv,
                    totalbytessent,
                    bandwidthRecv: 0,
                    bandwidthSent: 0,
                  },
                ];
              }

              const last = prevHistory[prevHistory.length - 1];
              const deltaTime = (timestamp - last.timestamp) / 1000;

              // Avoid divide-by-zero or negative time issues
              if (deltaTime <= 0) return prevHistory;

              const bandwidthRecv =
                (totalbytesrecv - last.totalbytesrecv) / deltaTime;
              const bandwidthSent =
                (totalbytessent - last.totalbytessent) / deltaTime;

              return [
                ...prevHistory.slice(-10), // keep last 10 entries
                {
                  timestamp,
                  bandwidthRecv,
                  bandwidthSent,
                  totalbytesrecv,
                  totalbytessent,
                },
              ];
            });
          }
        } catch (err) {
          console.error('Error parsing WebSocket message:', err);
        }
      };

      ws.onclose = () => {
        if (!isMounted) return;
        if (process.env.NODE_ENV !== 'test') {
          console.warn('WebSocket closed');
        }
        setWsConnected(false);

        if (reconnectAttempts < maxReconnectAttempts) {
          if (reconnectTimeoutRef.current) {
            clearTimeout(reconnectTimeoutRef.current); // ✅ prevent overlap
          }

          reconnectTimeoutRef.current = setTimeout(() => {
            reconnectAttempts++;
            connect();
          }, 1000 * reconnectAttempts);
        }
      };
    };

    connect();

    return () => {
      isMounted = false;
      if (reconnectTimeoutRef.current) {
        clearTimeout(reconnectTimeoutRef.current);
      }
      if (wsRef.current) {
        wsRef.current.onopen = null;
        wsRef.current.onclose = null;
        wsRef.current.onerror = null;
        wsRef.current.onmessage = null;
        if (wsRef.current.readyState === WebSocket.OPEN) {
          wsRef.current.close();
        }
      }
    };
  }, []);

  if (error) {
    return (
      <div className="min-h-auto bg-[#1e1e1e] text-white flex items-center justify-center">
        <div className="text-center">
          <p className="text-red-500 mb-4">{error}</p>
        </div>
      </div>
    );
  }

  if (
    loading ||
    !blockchainInfo ||
    !networkInfo ||
    !mempoolInfo ||
    !netTotals
  ) {
    return (
      <div className="flex items-center justify-center h-full w-full">
        <div className="flex flex-col items-center">
          <Loader className="h-8 w-8 text-[#0077B6] animate-spin" />
          <p className="mt-4 text-[#0077B6]">Loading...</p>
        </div>
      </div>
    );
  }

  const {
    blocks,
    headers,
    size_on_disk,
    bestblockhash,
    chain,
    verificationprogress,
    difficulty,
    pruned,
  } = blockchainInfo;

  const syncPercentage = ((blocks / headers) * 100).toFixed(2);

  return (
    <div className="bg-[#1e1e1e] px-4 sm:px-6 py-6">
      {/* Header */}
      <div className="flex flex-col sm:flex-row sm:items-start justify-between mb-10 gap-2">
        <div>
          <h1 className="text-2xl font-bold text-white tracking-tight">
            Node Health Dashboard
          </h1>
        </div>
        <div className="flex items-center gap-1.5 text-sm text-gray-500">
          <Clock className="w-3.5 h-3.5" />
          <span>Last updated: {lastUpdated}</span>
        </div>
      </div>

      {/* Summary Cards */}
      <div className="grid sm:grid-cols-1 md:grid-cols-4 gap-4">
        {/* Sync Status */}
        <div className="border border-gray-700 rounded-lg px-4 py-4 relative">
          <div className="absolute top-3 right-3 w-8 h-8 rounded-full bg-[#0d1f3c] flex items-center justify-center">
            <CheckCircle2 className="w-4 h-4 text-blue-400" />
          </div>
          <h2 className="text-sm text-gray-500 mb-1">Sync Status</h2>
          <p
            className={`text-2xl font-bold mb-3 ${headers === blocks ? 'text-green-500' : 'text-yellow-500'}`}
          >
            {headers === blocks ? 'Synced' : 'Syncing'}
          </p>
          <div className="flex justify-between text-sm text-gray-500 mb-1">
            <span>Sync Progress</span>
            <span>{syncPercentage}%</span>
          </div>
          <div className="w-full h-1 rounded bg-gray-800">
            <div
              className="h-full rounded bg-green-500"
              style={{ width: `${syncPercentage}%` }}
            />
          </div>
        </div>

        {/* Block Height */}
        <div className="border border-gray-700 rounded-lg px-4 py-4 relative">
          <div className="absolute top-3 right-3 w-8 h-8 rounded-full bg-[#0d1f3c] flex items-center justify-center">
            <Box className="w-4 h-4 text-blue-400" />
          </div>
          <h2 className="text-sm text-gray-500 mb-1">Block Height</h2>
          <p className="text-2xl text-white font-bold font-mono">{blocks}</p>
          <div className="mt-2 space-y-1">
            <div className="flex justify-between text-sm text-gray-500">
              <span>Headers</span>
              <span className="font-mono text-gray-400">{headers}</span>
            </div>
            <div className="flex justify-between text-sm text-gray-500">
              <span>Disk</span>
              <span className="font-mono text-gray-400">
                {(size_on_disk / 1024 ** 3).toFixed(2)} GB
              </span>
            </div>
          </div>
        </div>

        {/* Connections */}
        <div className="border border-gray-700 rounded-lg px-4 py-4 relative">
          <div className="absolute top-3 right-3 w-8 h-8 rounded-full bg-[#0d1f3c] flex items-center justify-center">
            <Users className="w-4 h-4 text-blue-400" />
          </div>
          <h2 className="text-sm text-gray-500 mb-1">Connections</h2>
          <p className="text-2xl text-white font-bold font-mono">
            {networkInfo?.connections ?? '...'}
          </p>
          <div className="mt-2 space-y-1">
            <div className="flex justify-between text-sm text-gray-500">
              <span>Inbound</span>
              <span className="font-mono text-gray-400">
                {networkInfo?.connections_in ?? '?'}
              </span>
            </div>
            <div className="flex justify-between text-sm text-gray-500">
              <span>Outbound</span>
              <span className="font-mono text-gray-400">
                {networkInfo?.connections_out ?? '?'}
              </span>
            </div>
          </div>
        </div>

        {/* Mempool */}
        <div className="border border-gray-700 rounded-lg px-4 py-4 relative">
          <div className="absolute top-3 right-3 w-8 h-8 rounded-full bg-[#0d1f3c] flex items-center justify-center">
            <Layers className="w-4 h-4 text-blue-400" />
          </div>
          <h2 className="text-sm text-gray-500 mb-1">Mempool</h2>
          <div className="flex items-baseline gap-1.5">
            <p className="text-2xl text-white font-bold font-mono">
              {mempoolInfo?.size?.toLocaleString() ?? '...'}
            </p>
            <span className="text-sm text-gray-600">txs</span>
          </div>
          <div className="flex justify-between text-sm text-gray-500 mb-1 mt-3">
            <span>Memory</span>
            <span>
              {mempoolInfo && mempoolInfo.usage
                ? `${(mempoolInfo.usage / (1024 * 1024)).toFixed(2)} MB`
                : '...'}
            </span>
          </div>
          <div className="w-full h-1 rounded bg-gray-800">
            <div
              className="h-full rounded bg-green-500"
              style={{
                width:
                  mempoolInfo && mempoolInfo.usage && mempoolInfo.maxmempool
                    ? `${((mempoolInfo.usage / mempoolInfo.maxmempool) * 100).toFixed(2)}%`
                    : '0%',
              }}
            />
          </div>
        </div>
      </div>

      {/* Tabs */}
      <div className="mt-6 border-b border-gray-700">
        <nav className="flex max-sm:flex-wrap gap-1 text-sm font-medium whitespace-nowrap">
          {TABS.map((tab) => (
            <button
              key={tab.value}
              className={`px-3 pb-2 pt-1 border-b-2 -mb-px ${activeTab === tab.value ? 'text-white border-blue-500' : 'text-gray-500 cursor-pointer border-transparent hover:text-gray-300'}`}
              onClick={() => setActiveTab(tab.value)}
            >
              {tab.label}
            </button>
          ))}
        </nav>
      </div>

      {/* Tab Content */}
      <div className="mt-6">
        {activeTab === 'blockchain' && blockchainInfo && (
          <div className="w-full">
            <div className="rounded-lg border border-gray-700 p-5">
              <div className="flex items-center gap-2 mb-5">
                <Link2 className="w-4 h-4 text-blue-400" />
                <h3 className="text-lg text-white font-semibold">
                  Blockchain Information
                </h3>
              </div>
              <div className="grid md:grid-cols-2 gap-6">
                <div className="space-y-3 text-sm">
                  <InfoRow label="Chain" value={chain} />
                  <InfoRow label="Blocks" value={blocks} mono />
                  <InfoRow label="Headers" value={headers} mono />
                  <div className="flex justify-between items-center">
                    <span className="text-gray-500">Synced</span>
                    <span
                      className={`px-2 py-0.5 rounded text-xs font-medium ${headers === blocks ? 'bg-green-900 text-green-400' : 'bg-yellow-900 text-yellow-400'}`}
                    >
                      {headers === blocks ? 'Yes' : 'No'}
                    </span>
                  </div>
                  <div className="pt-2 border-t border-gray-800 space-y-3">
                    <InfoRow
                      label="Verification"
                      value={`${(verificationprogress * 100).toFixed(4)}%`}
                      mono
                    />
                    <InfoRow label="Difficulty" value={difficulty} mono />
                    <div className="flex justify-between items-center">
                      <span className="text-gray-500">Pruned</span>
                      <span className="px-2 py-0.5 rounded text-xs font-medium bg-gray-800 text-gray-400">
                        {pruned ? 'Yes' : 'No'}
                      </span>
                    </div>
                  </div>
                </div>

                <div className="md:border-l md:border-gray-700 md:pl-6">
                  <p className="text-sm text-gray-500 mb-3">Best Block Hash</p>
                  <div className="flex items-start gap-2">
                    <p className="font-mono text-sm text-white break-all flex-1">
                      {isSmallScreen
                        ? shortenHash(bestblockhash)
                        : bestblockhash}
                    </p>
                    <button
                      onClick={() => copy(bestblockhash)}
                      className={`flex-shrink-0 p-1.5 rounded transition-colors ${
                        copied === bestblockhash
                          ? 'text-green-400'
                          : 'text-gray-500 hover:text-gray-300 hover:bg-gray-800'
                      }`}
                      aria-label={
                        copied === bestblockhash ? 'Copied!' : 'Copy block hash'
                      }
                    >
                      {copied === bestblockhash ? (
                        <Check className="w-3.5 h-3.5" />
                      ) : (
                        <Copy className="w-3.5 h-3.5" />
                      )}
                    </button>
                  </div>
                </div>
              </div>
            </div>
          </div>
        )}

        {activeTab === 'peers' && peerInfo && <Peers peers={peerInfo} />}
        {activeTab === 'mempool' && mempoolInfo && (
          <MempoolPanel mempool={mempoolInfo} />
        )}
        {activeTab === 'bandwidth' && (
          <div className="space-y-4">
            {networkInfo && <NetworkPanel network={networkInfo} />}
            <div className="space-y-6">
              <BandwidthPanel bandwidthHistory={bandwidthHistory} />
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default NodeHealth;
