import { useEffect, useRef, useState } from 'react';
import { formatWork } from '../lib/Utils';
import { PoolData } from '../lib/Types';
import { WEBSOCKET_URLS } from '@/URLs';
import { formatFeePercentage } from '../lib/Utils';

export function PoolDominance() {
  const [poolDominance, setPoolDominance] = useState<PoolData[]>([]);

  const wsRef = useRef<WebSocket | null>(null);
  const [wsConnected, setWsConnected] = useState(false);

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    let isMounted = true;
    wsRef.current = ws;

    ws.onopen = () => {
      if (!isMounted) return;
      setWsConnected(true);
    };
    ws.onerror = (error) => {
      setWsConnected(false);
      console.error('WebSocket error:', error);
    };
    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'pool_update') {
          setPoolDominance(message.data as PoolData[]);
        }
      } catch (err) {
        console.error('Error parsing websocket message :', err);
      }
    };

    ws.onclose = () => {
      if (!isMounted) return;
      console.log('WebSocket disconnected');
      setWsConnected(false);
    };
    return () => {
      isMounted = false;
      ws.onopen = null;
      ws.onclose = null;
      ws.onerror = null;
      ws.onmessage = null;
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, []);

  return (
    <div>
      <div className="flex justify-between items-center mt-4">
        <div className="flex items-center gap-2">
          <h2 className="text-white text-xl font-semibold">Pool Ranking</h2>
          <span className="bg-gray-700 text-gray-300 px-2 py-1 rounded text-xs w-fit mt-2">
            1 Week
          </span>
        </div>
      </div>

      <div className="mt-6">
        <div className="w-full">
          <div className="sm:hidden max-md:hidden  lg:block ">
            {/* Table Header */}
            <div className="grid grid-cols-8 gap-2 lg:gap-4 p-3 lg:p-4 border-b text-sm border-gray-800/80 font-medium">
              {[
                'Rank',
                'Pool',
                'Recent Block',
                'Hashrate',
                'Blocks',
                'Avg Health',
                'Avg Block Fees',
                'Empty Blocks',
              ].map((label) => (
                <div
                  key={label}
                  className="text-white font-semibold text-xs lg:text-sm"
                >
                  {label}
                </div>
              ))}
            </div>

            {/* Table Rows */}
            {poolDominance.map((pool, index) => (
              <div
                key={index}
                className="grid grid-cols-8 gap-2 lg:gap-4 text-xs lg:text-sm text-gray-300 py-3 lg:py-5 px-3 lg:px-4 hover:bg-gray-900/30 transition-colors"
              >
                <div>{pool.rank}</div>
                <div className="hover:text-blue-400 truncate">
                  <a
                    href={pool.poolLink}
                    target="_blank"
                    rel="noopener noreferrer"
                    title={pool.pool}
                  >
                    {pool.pool}
                  </a>
                </div>
                <div>{pool.latestBlockHeight}</div>
                <div className="truncate">
                  {formatWork(pool.hashrate).value}{' '}
                  {formatWork(pool.hashrate).unit}
                </div>
                <div>{pool.blocks}</div>
                <div>{pool.avgHealth}</div>
                <div
                  className={
                    typeof pool.avgBlockFees === 'string' &&
                    pool.avgBlockFees.startsWith('-')
                      ? 'text-red-500'
                      : 'text-green-400'
                  }
                >
                  {formatFeePercentage(pool.avgBlockFees)}
                </div>
                <div>{pool.emptyBlocks}</div>
              </div>
            ))}
          </div>

          {/* Mobile/Small Tablet Card View (sm and below) */}
          <div className=" lg:hidden px-2 sm:px-4">
            <div className="space-y-3 sm:space-y-4">
              {poolDominance.map((pool, index) => (
                <div
                  key={index}
                  className=" border border-gray-800 rounded-lg p-3 sm:p-4 space-y-2 sm:space-y-3"
                >
                  {/* Pool Header */}
                  <div className="flex justify-between items-start">
                    <div className="flex items-center gap-2">
                      <span className="bg-gray-700 text-white text-xs px-2 py-1 rounded font-medium">
                        #{pool.rank}
                      </span>
                      <h3 className="text-white font-semibold text-sm sm:text-base hover:text-blue-400">
                        <a
                          href={pool.poolLink}
                          target="_blank"
                          rel="noopener noreferrer"
                        >
                          {pool.pool}
                        </a>
                      </h3>
                    </div>
                  </div>

                  {/* Pool Stats Grid */}
                  <div className="grid grid-cols-2 gap-2 sm:gap-3 text-xs sm:text-sm">
                    <div>
                      <span className="text-gray-400">Recent Block:</span>
                      <div className="text-white font-medium">
                        {pool.latestBlockHeight}
                      </div>
                    </div>
                    <div>
                      <span className="text-gray-400">Hashrate:</span>
                      <div className="text-white font-medium">
                        {formatWork(pool.hashrate).value}{' '}
                        {formatWork(pool.hashrate).unit}
                      </div>
                    </div>
                    <div>
                      <span className="text-gray-400">Blocks:</span>
                      <div className="text-white font-medium">
                        {pool.blocks}
                      </div>
                    </div>
                    <div>
                      <span className="text-gray-400">Avg Health:</span>
                      <div className="text-white font-medium">
                        {pool.avgHealth}
                      </div>
                    </div>
                    <div>
                      <span className="text-gray-400">Avg Block Fees:</span>
                      <div
                        className={`font-medium ${
                          typeof pool.avgBlockFees === 'string' &&
                          pool.avgBlockFees.startsWith('-')
                            ? 'text-red-500'
                            : 'text-green-400'
                        }`}
                      >
                        {formatFeePercentage(pool.avgBlockFees)}
                      </div>
                    </div>
                    <div>
                      <span className="text-gray-400">Empty Blocks:</span>
                      <div className="text-white font-medium">
                        {pool.emptyBlocks}
                      </div>
                    </div>
                  </div>
                </div>
              ))}
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
