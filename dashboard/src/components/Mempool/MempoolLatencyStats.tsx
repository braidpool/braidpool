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
  Currency,
  Fee,
  BlockFeeHistoryItem,
  MempoolData,
  FeeDistributionItem,
} from './Types';
import { currencyLabels, currencyColors } from './Constants';
import { CURRENCIES, formatBtcAmount } from './Utils';
import { WEBSOCKET_URLS } from '@/URLs';
import { Loader, Download } from 'lucide-react';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';

const MempoolLatencyStats = () => {
  const wsRef = useRef<WebSocket | null>(null);

  const [mempoolData, setMempoolData] = useState<MempoolData | null>(null);
  const [currency, setCurrency] = useState<Currency>('USD');
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
  const formatFee = (fee: Fee | undefined) =>
    `${fee?.sats_per_vbyte ?? '--'} sats/vB | ${formatBtcAmount(
      fee?.fee_btc,
      currency,
      mempoolData.currency_rates
    )}`;
  const feeEstimates: [string, Fee | undefined][] = [
    ['High Priority', fees.high_priority],
    ['Medium Priority', fees.medium_priority],
    ['Low Priority', fees.standard_priority],
    ['No Priority', fees.economy],
  ];
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
        <div className="flex justify-end mb-4">
          <select
            aria-label="Display currency"
            value={currency}
            onChange={(e) => {
              const selected = CURRENCIES.find((c) => c === e.target.value);
              if (selected) setCurrency(selected);
            }}
            className="px-4 py-2 bg-[#1a1a1a] text-gray-300 rounded-md shadow-md border border-white"
          >
            {CURRENCIES.map((c) => (
              <option key={c} value={c}>
                {c}
              </option>
            ))}
          </select>
        </div>
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
            title={`Total Fees (${currency})`}
            value={formatBtcAmount(
              mempoolData?.mempool?.total_fee_btc,
              currency,
              mempoolData.currency_rates
            )}
          />
          <AnimatedStatCard
            title="Next Block Fees"
            value={formatFee(next)}
            color={colors.warning}
          />
        </div>

        {/* --- Fee Estimates --- */}
        <div className="mb-6">
          <h3 className="text-sm uppercase text-gray-400 mb-2">
            Fee Estimates
          </h3>
          <div className="grid sm:grid-cols-1 md:grid-cols-4 lg:grid-cols-4 gap-4">
            {feeEstimates.map(([title, fee]) => (
              <AnimatedStatCard
                key={title}
                title={title}
                value={formatFee(fee)}
              />
            ))}
          </div>
        </div>

        {/* --- Fee Rate Distribution --- */}
        <div className="shadow p-6 relative">
          <div className="absolute right-3 top-3 z-10">
            <button
              onClick={handleDownloadFeeDist}
              className="p-1.5 rounded text-gray-500 hover:text-gray-300 hover:bg-gray-800 transition-colors"
              aria-label="Download fee distribution chart"
            >
              <Download className="w-4 h-4" />
            </button>
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
          <button
            onClick={handleDownloadBlockFees}
            className="p-1.5 rounded text-gray-500 hover:text-gray-300 hover:bg-gray-800 transition-colors"
            aria-label="Download block fees chart"
          >
            <Download className="w-4 h-4" />
          </button>
        </div>
        <div className="flex justify-between items-center mb-4 flex-wrap pt-4">
          <h2 className="text-lg font-semibold">Live Block Fees</h2>

          <select
            aria-label="Block fee chart currency"
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
