import React, { useState, useEffect, useRef } from 'react';
import Peers from './Peers';
import NetworkPanel from './Network';
import MempoolPanel from './Mempool';
import BandwidthPanel from './Bandwidth';
import { InfoRow } from './InfoRow';
import { TABS, useIsSmallScreen } from './Utils';
import { shortenHash } from '../BeadsTab/lib/Utils';

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

  useEffect(() => {
    let isMounted = true;
    let reconnectAttempts = 0;
    const maxReconnectAttempts = 5;

    const connect = () => {
      const ws = new WebSocket('ws://localhost:5000');
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
      <div className="min-h-auto bg-[#1e1e1e] text-white flex items-center justify-center">
        Loading...
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
    <div className="min-h-auto bg-[#1e1e1e] px-2 sm:px-4 md:px-6 py-6 md:py-8">
      <div>
        <p className="text-xs flex justify-end sm:text-sm text-gray-500 mb-4">
          {`Last updated: ${lastUpdated}`}
        </p>
      </div>

      {/* Summary Cards */}
      <div className="grid sm:grid-cols-1  md:grid-cols-4 gap-4 md:gap-6">
        {/* Sync Status */}
        <div className=" border border-gray-700 rounded-xl px-2 py-2">
          <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Sync Status</h2>
          <p
            className={`text-lg sm:text-xl font-bold mb-1 ${headers === blocks ? 'text-green-600' : 'text-yellow-500'}`}
          >
            {headers === blocks ? 'Synced' : 'Syncing'}
          </p>
          <div className="w-full h-4 rounded bg-gray-200">
            <div
              className="h-full rounded bg-green-500"
              style={{ width: `${syncPercentage}%` }}
            ></div>
          </div>
          <p className="text-xs text-gray-500 mt-1">
            {syncPercentage}% complete
          </p>
        </div>

        {/* Block Height */}
        <div className=" border border-gray-700 rounded-xl px-2 py-2">
          <h2 className="text-xs sm:text-sm text-gray-500 mb-1">
            Block Height
          </h2>
          <p className="text-lg sm:text-xl text-white font-bold">{blocks}</p>
          <p className="text-xs text-gray-500">
            {(size_on_disk / 1024 ** 3).toFixed(2)}GB
          </p>
        </div>

        {/* Connections */}
        <div className=" border border-gray-700 rounded-xl px-2 py-2">
          <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Connections</h2>
          <p className="text-lg sm:text-xl text-white font-bold">
            {networkInfo?.connections ?? '...'}
          </p>
          <p className="text-xs text-gray-500">
            {networkInfo
              ? `${networkInfo.connections_in ?? '?'} inbound, ${networkInfo.connections_out ?? '?'} outbound`
              : ''}
          </p>
        </div>

        {/* Mempool */}
        <div className="border border-gray-700 rounded-xl px-2 py-2">
          <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Mempool</h2>
          <p className="text-lg sm:text-xl text-white font-bold">
            {mempoolInfo?.size?.toLocaleString() ?? '...'}
          </p>
          <div className="w-full h-4 rounded bg-gray-200">
            <div
              className="h-full rounded bg-green-500"
              style={{
                width:
                  mempoolInfo && mempoolInfo.usage && mempoolInfo.maxmempool
                    ? `${((mempoolInfo.usage / mempoolInfo.maxmempool) * 100).toFixed(2)}%`
                    : '0%',
              }}
            ></div>
          </div>
          <p className="text-xs text-gray-500 mt-1">
            {mempoolInfo && mempoolInfo.usage
              ? `${(mempoolInfo.usage / (1024 * 1024)).toFixed(2)} MB`
              : '...'}
          </p>
        </div>
      </div>

      {/* Tabs */}
      <div className="mt-8 border border-gray-700 rounded-xl p-3 flex justify-center">
        <nav className="flex max-sm:flex-col gap-4 sm:gap-10 text-xs sm:text-sm font-medium whitespace-nowrap">
          {TABS.map((tab) => (
            <button
              key={tab.value}
              className={`py-2 border-b-2 ${activeTab === tab.value ? 'text-white border-blue-900' : 'text-gray-500 border-transparent'}`}
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
          <div className="grid grid-cols-1 md:grid-cols-2 gap-4 mt-6">
            <div className="rounded-xl border border-gray-700 p-4">
              <h3 className="text-base md:text-lg text-white font-semibold text-center mb-4">
                Blockchain Information
              </h3>
              <div className="space-y-2 text-xs sm:text-sm">
                <InfoRow label="Chain" value={chain} />
                <InfoRow label="Current Blocks" value={blocks} />
                <InfoRow
                  label="Synced"
                  value={headers === blocks ? 'True' : 'False'}
                />
                <InfoRow
                  label="Best Block Hash"
                  value={
                    isSmallScreen ? shortenHash(bestblockhash) : bestblockhash
                  }
                />
                <InfoRow
                  label="Verification Progress"
                  value={`${(verificationprogress * 100).toFixed(4)}%`}
                />
                <InfoRow label="Difficulty" value={difficulty} />
                <InfoRow label="Pruned" value={pruned ? 'True' : 'False'} />
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
