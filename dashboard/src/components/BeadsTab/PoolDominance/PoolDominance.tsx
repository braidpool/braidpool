import { useEffect, useRef, useState } from 'react';
import { formatWork } from '../lib/Utils';
import { PoolData } from '../lib/Types';
import { PieChart, Pie, Cell, Tooltip, ResponsiveContainer } from 'recharts';
import { COLORS } from '../lib/Constants';

export function PoolDominance() {
  const [activeTab, setActiveTab] = useState<'overview' | 'visualize'>(
    'overview'
  );
  const [poolDominance, setPoolDominance] = useState<PoolData[]>([]);

  const wsRef = useRef<WebSocket | null>(null);
  const [wsConnected, setWsConnected] = useState(false);
  const pieData = (() => {
    if (!poolDominance || poolDominance.length === 0) return [];

    const sorted = [...poolDominance].sort((a, b) => b.hashrate - a.hashrate);
    const top9 = sorted.slice(0, 9);
    const others = sorted.slice(9);

    const othersHashrate = others.reduce((sum, item) => sum + item.hashrate, 0);

    return [
      ...top9,
      ...(others.length > 0
        ? [{ pool: 'Others', hashrate: othersHashrate }]
        : []),
    ];
  })();

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');
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
    <div className=" ">
      <div className="flex justify-between items-center mt-4">
        <div className="flex items-center gap-4">
          <h2 className="text-white text-xl font-semibold">Pool Dominance</h2>
          <span className="bg-gray-700 text-gray-300 px-2 py-1 rounded text-xs mt-2">
            1 Week
          </span>
        </div>
        <div className="flex space-x-4 mb-4">
          {['overview', 'visualize'].map((tab) => (
            <button
              key={tab}
              className={`px-4 py-2 rounded-lg ${
                activeTab === tab
                  ? 'bg-gray-700 text-white'
                  : 'bg-black text-gray-300'
              }`}
              onClick={() => setActiveTab(tab as 'overview' | 'visualize')}
            >
              {tab.charAt(0).toUpperCase() + tab.slice(1)}
            </button>
          ))}
        </div>
      </div>
      {/* overview */}
      <div className=" gap-6">
        {activeTab === 'overview' && (
          <>
            <div className="grid max-sm:grid-cols-3  md:grid-cols-7 p-4 border-b text-sm border-gray-800/80 font-medium">
              {[
                'Rank',
                'Pool',
                'Hashrate',
                'Blocks',
                'Avg Health',
                'Avg Block Fees',
                'Empty Blocks',
              ].map((label) => (
                <div key={label} className="text-white font-semibold">
                  {label}
                </div>
              ))}
            </div>

            {poolDominance.map((pool, index) => (
              <div
                key={index}
                className="grid grid-cols-7 gap-4 text-sm text-gray-300 py-5"
              >
                <div className="ml-6">{pool.rank}</div>
                <div>{pool.pool}</div>
                <div>
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
                  {parseFloat(String(pool.avgBlockFees)) * 100 < 0
                    ? `${(parseFloat(String(pool.avgBlockFees)) * -100).toFixed(
                        2
                      )}%`
                    : `${(parseFloat(String(pool.avgBlockFees)) * 100).toFixed(
                        2
                      )}%`}
                </div>
                <div>{pool.emptyBlocks}</div>
              </div>
            ))}
          </>
        )}
      </div>
      {/* visualize */}
      {activeTab === 'visualize' && (
        <div>
          <ResponsiveContainer width="100%" height={400}>
            <PieChart>
              <Pie
                data={pieData}
                dataKey="hashrate"
                nameKey="pool"
                cx="50%"
                cy="50%"
                outerRadius={160}
                innerRadius={60}
                paddingAngle={2}
                isAnimationActive={false}
                labelLine={false}
                animationBegin={0}
                animationDuration={0}
                label={({
                  cx,
                  cy,
                  midAngle,
                  innerRadius,
                  outerRadius,
                  percent,
                  name,
                }) => {
                  if (percent < 0.03) return null; // Hide labels for very small slices

                  const RADIAN = Math.PI / 180;
                  const radius =
                    innerRadius + (outerRadius - innerRadius) * 1.2;
                  const x = cx + radius * Math.cos(-midAngle * RADIAN);
                  const y = cy + radius * Math.sin(-midAngle * RADIAN);

                  return (
                    <text
                      x={x}
                      y={y}
                      fill="white"
                      textAnchor={x > cx ? 'start' : 'end'}
                      dominantBaseline="central"
                      fontSize={12}
                      fontWeight="500"
                      className="drop-shadow-lg"
                    >
                      {`${name}`}
                    </text>
                  );
                }}
              >
                {poolDominance.map((_, index) => (
                  <Cell
                    key={`cell-${index}`}
                    fill={COLORS[index % COLORS.length]}
                    stroke="#1c1c1c"
                    strokeWidth={2}
                  />
                ))}
              </Pie>
              <Tooltip
                content={({ active, payload }) => {
                  if (active && payload && payload.length) {
                    const data = payload[0].payload;
                    return (
                      <div className="bg-black border border-gray-700 rounded-lg p-4 shadow-lg">
                        <h3 className="text-white font-semibold text-lg mb-2">
                          {data.pool}
                        </h3>
                        <div className="space-y-1 text-sm">
                          <div className="flex justify-between items-center">
                            <span className="text-gray-300">Hashrate:</span>
                            <span className="text-white font-medium">
                              {formatWork(data.hashrate).value}{' '}
                              {formatWork(data.hashrate).unit}
                            </span>
                          </div>
                          <div className="flex justify-between items-center">
                            <span className="text-gray-300">Share:</span>
                            <span className="text-white font-medium">
                              {data.percentage
                                ? data.percentage.toFixed(2)
                                : (
                                    (data.hashrate /
                                      poolDominance.reduce(
                                        (sum, p) => sum + p.hashrate,
                                        0
                                      )) *
                                    100
                                  ).toFixed(2)}
                              %
                            </span>
                          </div>
                          <div className="flex justify-between items-center">
                            <span className="text-gray-300">Blocks:</span>
                            <span className="text-white font-medium">
                              {data.blocks}
                            </span>
                          </div>
                          <div className="flex justify-between items-center">
                            <span className="text-gray-300">Health:</span>
                            <span className="text-white font-medium">
                              {data.avgHealth}
                            </span>
                          </div>
                          <div className="flex justify-between items-center">
                            <span className="text-gray-300">Block Fees:</span>
                            <span
                              className={`font-medium ${
                                typeof data.avgBlockFees === 'string' &&
                                data.avgBlockFees.startsWith('-')
                                  ? 'text-red-400'
                                  : 'text-green-400'
                              }`}
                            >
                              {(
                                parseFloat(String(data.avgBlockFees)) * 100
                              ).toFixed(3)}
                              %
                            </span>
                          </div>
                          <div className="flex justify-between items-center">
                            <span className="text-gray-300">Empty Blocks:</span>
                            <span className="text-white font-medium">
                              {data.emptyBlocks}
                            </span>
                          </div>
                        </div>
                      </div>
                    );
                  }
                  return null;
                }}
              />
            </PieChart>
          </ResponsiveContainer>
        </div>
      )}
    </div>
  );
}
