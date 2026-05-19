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
  MempoolStats,
  FeeDistributionItem,
} from './Types';
import { currencyLabels, currencyColors, currencyFullNames } from './Constants';
import { WEBSOCKET_URLS } from '@/URLs';
import { Loader } from 'lucide-react';
import ActionIconButton from '../common/ActionIconButton';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';

type Currency =
  | 'btc'
  | 'usd'
  | 'eur'
  | 'jpy'
  | 'gbp'
  | 'cad'
  | 'aud'
  | 'chf'
  | 'inr'
  | 'krw'
  | 'brl'
  | 'hkd'
  | 'sgd';

const CURRENCIES: Currency[] = [
  'btc',
  'usd',
  'eur',
  'jpy',
  'gbp',
  'cad',
  'aud',
  'chf',
  'inr',
  'krw',
  'brl',
  'hkd',
  'sgd',
];

const TOTAL_FEE_KEY_BY_CURRENCY: Record<Currency, keyof MempoolStats> = {
  btc: 'total_fee_btc',
  usd: 'total_fee_usd',
  eur: 'total_fee_eur',
  jpy: 'total_fee_jpy',
  gbp: 'total_fee_gbp',
  cad: 'total_fee_cad',
  aud: 'total_fee_aud',
  chf: 'total_fee_chf',
  inr: 'total_fee_inr',
  krw: 'total_fee_krw',
  brl: 'total_fee_brl',
  hkd: 'total_fee_hkd',
  sgd: 'total_fee_sgd',
};

const formatAmountPreserveNonZero = (
  value: number,
  defaultDecimals: number
): string => {
  if (!Number.isFinite(value)) {
    return '--';
  }

  if (value === 0) {
    return value.toFixed(defaultDecimals);
  }

  const absValue = Math.abs(value);
  const roundingThreshold = Math.pow(10, -defaultDecimals);

  if (absValue >= roundingThreshold) {
    return value.toFixed(defaultDecimals);
  }

  const adaptiveDecimals = Math.min(20, Math.ceil(-Math.log10(absValue)) + 2);
  return value.toFixed(adaptiveDecimals).replace(/\.?0+$/, '');
};

const toFiniteNumber = (value: unknown): number | null => {
  if (value === null || value === undefined) {
    return null;
  }

  const parsed = Number(value);
  return Number.isFinite(parsed) ? parsed : null;
};

// Format a fee amount for display in stat cards and chart tooltips
const CURRENCY_FORMAT: Record<Currency, (v: number) => string> = {
  btc: (v) => `${formatAmountPreserveNonZero(Number(v), 8)} BTC`,
  usd: (v) => `$${formatAmountPreserveNonZero(Number(v), 2)}`,
  eur: (v) => `€${formatAmountPreserveNonZero(Number(v), 2)}`,
  jpy: (v) => `¥${formatAmountPreserveNonZero(Number(v), 0)}`,
  gbp: (v) => `£${formatAmountPreserveNonZero(Number(v), 2)}`,
  cad: (v) => `CA$${formatAmountPreserveNonZero(Number(v), 2)}`,
  aud: (v) => `A$${formatAmountPreserveNonZero(Number(v), 2)}`,
  chf: (v) => `CHF ${formatAmountPreserveNonZero(Number(v), 2)}`,
  inr: (v) => `₹${formatAmountPreserveNonZero(Number(v), 0)}`,
  krw: (v) => `₩${formatAmountPreserveNonZero(Number(v), 0)}`,
  brl: (v) => `R$${formatAmountPreserveNonZero(Number(v), 2)}`,
  hkd: (v) => `HK$${formatAmountPreserveNonZero(Number(v), 2)}`,
  sgd: (v) => `S$${formatAmountPreserveNonZero(Number(v), 2)}`,
};

const MempoolLatencyStats = () => {
  const wsRef = useRef<WebSocket | null>(null);

  const [mempoolData, setMempoolData] = useState<MempoolData | null>(null);
  const [selectedCurrency, setSelectedCurrency] = useState<Currency>('btc');
  const [blockFeeHistory, setBlockFeeHistory] = useState<BlockFeeHistoryItem[]>(
    []
  );
  const [wsConnected, setWsConnected] = useState(false);
  const [wsStatusMessage, setWsStatusMessage] = useState(
    'Connecting to live mempool feed...'
  );
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
      setWsStatusMessage('');
      console.log('[WebSocket] Connected');
    };
    ws.onerror = (err) => {
      setWsConnected(false);
      setWsStatusMessage('Live updates unavailable. Retrying connection...');
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
      setWsStatusMessage('Disconnected from live updates.');
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
          {!wsConnected && wsStatusMessage ? (
            <p className="mt-2 text-sm text-gray-400">{wsStatusMessage}</p>
          ) : null}
        </div>
      </div>
    );
  }

  const fees = mempoolData?.fees || {};
  const next: Fee | undefined = mempoolData?.next_block_fees;
  const feeDist = mempoolData?.fee_distribution || {};

  const formatTotalFee = (currency: Currency): string => {
    const m = mempoolData?.mempool;
    if (!m) return '--';

    const totalFeeKey = TOTAL_FEE_KEY_BY_CURRENCY[currency];
    const amount = toFiniteNumber(m[totalFeeKey]);

    if (amount === null) {
      return '--';
    }

    return CURRENCY_FORMAT[currency](amount);
  };

  const formatFee = (fee: Fee | undefined, currency: Currency): string => {
    if (!fee) return '--';
    const sats = fee.sats_per_vbyte ?? '--';
    const rawAmount =
      currency === 'btc'
        ? fee.fee_btc
        : (fee as unknown as Record<string, unknown>)[`fee_${currency}`];

    const amount = toFiniteNumber(rawAmount);
    if (amount === null) {
      return `${sats} sats/vB | --`;
    }

    return `${sats} sats/vB | ${CURRENCY_FORMAT[currency](amount)}`;
  };

  const feeDistChartData: FeeDistributionItem[] = Object.entries(feeDist).map(
    ([label, value]) => ({
      name: label,
      value: value || 0,
    })
  );

  const blockFeeChartData = blockFeeHistory.map(
    (item: BlockFeeHistoryItem) => ({
      time: item.time || String(item.timestamp || ''),
      ...CURRENCIES.reduce(
        (acc, c) => {
          const raw = (item as unknown as Record<string, unknown>)[c];
          const value = Number(raw);
          acc[c] = Number.isFinite(value) ? value : null;
          return acc;
        },
        {} as Record<string, number | null>
      ),
    })
  );

  return (
    <div className="flex flex-col gap-8 p-6 text-gray-100">
      {/* --- Overview --- */}
      <section className="rounded-xl p-3 shadow-sm">
        <div className="flex justify-between items-center mb-4">
          <h2 className="text-lg font-semibold text-gray-100">Overview</h2>
          <select
            value={selectedCurrency}
            onChange={(e) => setSelectedCurrency(e.target.value as Currency)}
            aria-label="Overview currency"
            title={`Select overview currency (${currencyFullNames[selectedCurrency]})`}
            className="bg-[#1a1a1a] text-gray-300 px-4 py-2 rounded-md shadow-md border border-white text-sm"
          >
            {CURRENCIES.map((c) => (
              <option key={c} value={c} title={currencyFullNames[c]}>
                {currencyLabels[c]}
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
            title={`Total Fees (${currencyLabels[selectedCurrency]})`}
            value={formatTotalFee(selectedCurrency)}
          />
          <AnimatedStatCard
            title="Next Block Fees"
            value={formatFee(next, selectedCurrency)}
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
              value={formatFee(fees.high_priority, selectedCurrency)}
            />
            <AnimatedStatCard
              title="Medium Priority"
              value={formatFee(fees.medium_priority, selectedCurrency)}
            />
            <AnimatedStatCard
              title="Low Priority"
              value={formatFee(fees.standard_priority, selectedCurrency)}
            />
            <AnimatedStatCard
              title="No Priority"
              value={formatFee(fees.economy, selectedCurrency)}
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
                formatter={(value: unknown, name: string) => {
                  const label = currencyLabels[name] || name.toUpperCase();
                  const numericValue = toFiniteNumber(value);

                  if (numericValue === null) {
                    return ['--', label];
                  }

                  return [
                    CURRENCY_FORMAT[name as Currency]?.(numericValue) ??
                      `${numericValue.toFixed(2)}`,
                    label,
                  ];
                }}
              />
              <Legend />

              {CURRENCIES.map((c) => {
                const show = selectedCurrency === c;
                return show ? (
                  <Line
                    key={c}
                    type="monotone"
                    dataKey={c}
                    stroke={currencyColors[c]}
                    strokeWidth={2}
                    dot={{ r: 4 }}
                    name={c}
                  />
                ) : null;
              })}
            </LineChart>
          </ResponsiveContainer>
        </div>
      </section>
    </div>
  );
};

export default MempoolLatencyStats;
