import { useEffect, useState, useRef } from 'react';
import colors from '../../theme/colors';
import AnimatedStatCard from '../BeadsTab/AnimatedStatCard';
import {
  LineChart,
  Line,
  Legend,
  BarChart,
  Bar,
  XAxis,
  YAxis,
  Tooltip,
  ResponsiveContainer,
  CartesianGrid,
} from 'recharts';
import {
  Fee,
  BlockFeeHistoryItem,
  MempoolData,
  FeeDistributionItem,
} from './Types';
import { currencyLabels, currencyColors } from './Constants';
import { WEBSOCKET_URLS } from '@/URLs';
import { Loader } from 'lucide-react';
import ActionIconButton from '../common/ActionIconButton';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';

const MempoolLatencyStats = () => {
  const wsRef = useRef<WebSocket | null>(null);

  const [mempoolData, setMempoolData] = useState<MempoolData | null>(null);
  const [selectedView, setSelectedView] = useState<
    'btc' | 'usd' | 'eur' | 'jpy' | 'all'
  >('all');
  const [blockFeeHistory, setBlockFeeHistory] = useState<BlockFeeHistoryItem[]>(
    []
  );
  const [wsConnected, setWsConnected] = useState(false);
  const feeDistChartRef = useRef<HTMLDivElement | null>(null);
  const blockFeeChartRef = useRef<HTMLDivElement | null>(null);

  const handleDownloadFeeDist = () => {
    if (!feeDistChartRef.current) return;
    downloadSvgFromContainer(
      feeDistChartRef.current,
      'mempool-fee-distribution'
    );
  };

  const handleDownloadBlockFees = () => {
    if (!blockFeeChartRef.current) return;
    downloadSvgFromContainer(blockFeeChartRef.current, 'mempool-block-fees');
  };

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    wsRef.current = ws;
    ws.onopen = () => {
      setWsConnected(true);
      console.log('[WebSocket] Connected');
    };
    ws.onerror = (err) => {
      setWsConnected(false);
      console.error('[WebSocket] Error:', err);
    };
    ws.onmessage = (event) => {
      try {
        const msg = JSON.parse(event.data);
        if (msg.type === 'mempool_update') {
          const data = msg.data;
          setMempoolData(data);
          const latest = data?.block_fee_history?.[0];
          if (latest) {
            setBlockFeeHistory((prev) => {
              const isDuplicate = prev.some(
                (item) => item.height === latest.height
              );
              if (isDuplicate) return prev;

              const newHistory = [...prev, latest];
              return newHistory.slice(-50).sort((a, b) => {
                const aTime = a.timestamp || new Date(a.time).getTime() / 1000;
                const bTime = b.timestamp || new Date(b.time).getTime() / 1000;
                return aTime - bTime;
              });
            });
          }
        }
      } catch (e) {
        console.error('WebSocket message parse error:', e);
      }
    };

    ws.onclose = () => {
      setWsConnected(false);
      console.log('[WebSocket] Disconnected');
    };

    return () => {
      ws.onopen = null;
      ws.onclose = null;
      ws.onerror = null;
      ws.onmessage = null;
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, []);

  if (!mempoolData) {
    return (
      <div className="flex items-center justify-center h-full w-full">
        <div className="flex flex-col items-center">
          <Loader className="h-8 w-8 text-[#0077B6] animate-spin" />
          <p className="mt-4 text-[#0077B6]">Loading Mempool Stats...</p>
        </div>
      </div>
    );
  }

  const fees = mempoolData?.fees || {};
  const next: Fee | undefined = mempoolData?.next_block_fees;
  const feeDist = mempoolData?.fee_distribution || {};

  const feeDistChartData: FeeDistributionItem[] = Object.entries(feeDist).map(
    ([label, value]) => ({
      name: label,
      value: value || 0,
    })
  );

  const blockFeeChartData = blockFeeHistory.map(
    (item: BlockFeeHistoryItem) => ({
      time: item.time || String(item.timestamp || ''),
      btc: isNaN(Number(item.btc)) ? 0 : Number(item.btc),
      usd: isNaN(Number(item.usd)) ? 0 : Number(item.usd),
      eur: isNaN(Number(item.eur)) ? 0 : Number(item.eur),
      jpy: isNaN(Number(item.jpy)) ? 0 : Number(item.jpy),
    })
  );

  return (
    <div className="flex flex-col gap-8 p-6 text-gray-100">
      {/* --- Overview --- */}
      <section className="rounded-xl p-3 shadow-sm">
        <div className="grid sm:grid-cols-1 md:grid-cols-4 gap-4 mb-6">
          <AnimatedStatCard
            title="Size (vB)"
            value={String(mempoolData?.mempool?.vsize || '--')}
          />
          <AnimatedStatCard
            title="Transactions"
            value={String(mempoolData?.mempool?.count || '--')}
          />
          <AnimatedStatCard
            title="Total Fees (BTC | USD)"
            value={`${Number(mempoolData?.mempool?.total_fee_btc).toFixed(6)} BTC | $${Number(
              mempoolData?.mempool?.total_fee_usd
            ).toFixed(2)}`}
          />
          <AnimatedStatCard
            title="Next Block Fees"
            value={`${next?.sats_per_vbyte ?? '--'} sats/vB | $${Number(
              next?.fee_usd ?? 0
            ).toFixed(4)}`}
            color={colors.warning}
          />
        </div>

        {/* --- Fee Estimates --- */}
        <div className="mb-6">
          <h3 className="text-sm uppercase text-gray-400 mb-2">
            Fee Estimates
          </h3>
          <div className="grid sm:grid-cols-1 md:grid-cols-4 lg:grid-cols-4 gap-4">
            <AnimatedStatCard
              title="High Priority"
              value={`${fees.high_priority?.sats_per_vbyte || '--'} sats/vB | ${Number(
                fees.high_priority?.fee_btc
              ).toFixed(
                8
              )} BTC | $${Number(fees.high_priority?.fee_usd).toFixed(4)}`}
            />
            <AnimatedStatCard
              title="Medium Priority"
              value={`${fees.medium_priority?.sats_per_vbyte || '--'} sats/vB | ${Number(
                fees.medium_priority?.fee_btc
              ).toFixed(
                8
              )} BTC | $${Number(fees.medium_priority?.fee_usd).toFixed(4)}`}
            />
            <AnimatedStatCard
              title="Low Priority"
              value={`${fees.standard_priority?.sats_per_vbyte || '--'} sats/vB | ${Number(
                fees.standard_priority?.fee_btc
              ).toFixed(
                8
              )} BTC | $${Number(fees.standard_priority?.fee_usd).toFixed(4)}`}
            />
            <AnimatedStatCard
              title="No Priority"
              value={`${fees.economy?.sats_per_vbyte || '--'} sats/vB | ${Number(
                fees.economy?.fee_btc
              ).toFixed(8)} BTC | $${Number(fees.economy?.fee_usd).toFixed(4)}`}
            />
          </div>
        </div>

        {/* --- Fee Rate Distribution --- */}
        <div className="shadow p-6 relative">
          <div className="absolute right-3 top-3 z-10">
            <ActionIconButton
              onClick={handleDownloadFeeDist}
              icon={
                <svg
                  xmlns="http://www.w3.org/2000/svg"
                  viewBox="0 0 20 20"
                  fill="currentColor"
                >
                  <path d="M3 14.5A2.5 2.5 0 0 0 5.5 17h9a2.5 2.5 0 0 0 2.5-2.5V11a.75.75 0 0 0-1.5 0v3.5a1 1 0 0 1-1 1h-9a1 1 0 0 1-1-1V11a.75.75 0 0 0-1.5 0v3.5Z" />
                  <path d="M10 2a.75.75 0 0 0-.75.75v8.19L7.53 9.22a.75.75 0 0 0-1.06 1.06l3 3a.75.75 0 0 0 1.06 0l3-3a.75.75 0 1 0-1.06-1.06L10.75 10.94V2.75A.75.75 0 0 0 10 2Z" />
                </svg>
              }
            />
          </div>
          <h3 className="text-lg font-semibold text-center mb-4">
            Live Fee Rate Distribution
          </h3>
          <div className="h-64" ref={feeDistChartRef}>
            <ResponsiveContainer width="100%" height="100%">
              <BarChart data={feeDistChartData}>
                <CartesianGrid strokeDasharray="3 3" stroke="#374151" />
                <XAxis dataKey="name" stroke="#9ca3af" />
                <YAxis stroke="#9ca3af" />
                <Tooltip
                  contentStyle={{
                    backgroundColor: '#1f2937',
                    borderRadius: '8px',
                    border: 'none',
                    color: '#ffffff',
                    padding: '10px',
                    fontSize: '14px',
                  }}
                />
                <Bar dataKey="value" fill={colors.primary} />
              </BarChart>
            </ResponsiveContainer>
          </div>
        </div>
      </section>

      {/* --- Block Fee Chart --- */}
      <section className="shadow p-6 relative">
        <div className="absolute right-3 top-0 z-10">
          <ActionIconButton
            onClick={handleDownloadBlockFees}
            icon={
              <svg
                xmlns="http://www.w3.org/2000/svg"
                viewBox="0 0 20 20"
                fill="currentColor"
              >
                <path d="M3 14.5A2.5 2.5 0 0 0 5.5 17h9a2.5 2.5 0 0 0 2.5-2.5V11a.75.75 0 0 0-1.5 0v3.5a1 1 0 0 1-1 1h-9a1 1 0 0 1-1-1V11a.75.75 0 0 0-1.5 0v3.5Z" />
                <path d="M10 2a.75.75 0 0 0-.75.75v8.19L7.53 9.22a.75.75 0 0 0-1.06 1.06l3 3a.75.75 0 0 0 1.06 0l3-3a.75.75 0 1 0-1.06-1.06L10.75 10.94V2.75A.75.75 0 0 0 10 2Z" />
              </svg>
            }
          />
        </div>
        <div className="flex justify-between items-center mb-4 flex-wrap pt-4">
          <h2 className="text-lg font-semibold">Live Block Fees</h2>

          <select
            value={selectedView}
            onChange={(e) =>
              setSelectedView(e.target.value as typeof selectedView)
            }
            className="px-4 py-2 bg-[#1a1a1a] text-gray-300 rounded-md shadow-md border border-white"
          >
            <option value={selectedView} hidden disabled>
              {selectedView.toUpperCase()}
            </option>
            {(['btc', 'usd', 'eur', 'jpy', 'all'] as const)
              .filter((view) => view !== selectedView)
              .map((view) => (
                <option key={view} value={view}>
                  {view.toUpperCase()}
                </option>
              ))}
          </select>
        </div>

        <div ref={blockFeeChartRef}>
          <ResponsiveContainer width="100%" height={400}>
            <LineChart data={blockFeeChartData}>
              <CartesianGrid strokeDasharray="3 3" stroke="#374151" />
              <XAxis dataKey="time" stroke="#9ca3af" />
              <YAxis stroke="#9ca3af" />
              <Tooltip
                contentStyle={{
                  backgroundColor: '#1f2937',
                  borderRadius: '8px',
                  border: 'none',
                  color: '#ffffff',
                  padding: '15px',
                  fontSize: '14px',
                }}
                formatter={(value: number, name: string) => [
                  name === 'btc'
                    ? `${Number(value).toFixed(6)} BTC`
                    : name === 'jpy'
                      ? `¥${Number(value).toFixed(0)}`
                      : name === 'eur'
                        ? `€${Number(value).toFixed(2)}`
                        : name === 'usd'
                          ? `${Number(value).toFixed(2)}`
                          : `${Number(value).toFixed(2)}`,
                  currencyLabels[name] || name,
                ]}
              />
              <Legend />

              {(selectedView === 'btc' || selectedView === 'all') && (
                <Line
                  type="monotone"
                  dataKey="btc"
                  stroke={currencyColors.btc}
                  strokeWidth={2}
                  dot={{ r: 4 }}
                  name="BTC"
                />
              )}
              {(selectedView === 'usd' || selectedView === 'all') && (
                <Line
                  type="monotone"
                  dataKey="usd"
                  stroke={currencyColors.usd}
                  strokeWidth={2}
                  dot={{ r: 4 }}
                  name="USD"
                />
              )}
              {(selectedView === 'eur' || selectedView === 'all') && (
                <Line
                  type="monotone"
                  dataKey="eur"
                  stroke={currencyColors.eur}
                  strokeWidth={2}
                  dot={{ r: 4 }}
                  name="EUR"
                />
              )}
              {(selectedView === 'jpy' || selectedView === 'all') && (
                <Line
                  type="monotone"
                  dataKey="jpy"
                  stroke={currencyColors.jpy}
                  strokeWidth={2}
                  dot={{ r: 4 }}
                  name="JPY"
                />
              )}
            </LineChart>
          </ResponsiveContainer>
        </div>
      </section>
    </div>
  );
};

export default MempoolLatencyStats;
