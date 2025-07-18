import { useEffect, useState } from 'react';
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

const StatItem = ({
  label,
  value,
  color,
}: {
  label: string;
  value: string | number;
  color?: string;
}) => (
  <div className="mb-4">
    <p className="text-xs mb-1" style={{ color: colors.textSecondary }}>
      {label}
    </p>
    <p
      className="text-lg font-medium"
      style={{ color: color || colors.textPrimary }}
    >
      {value}
    </p>
  </div>
);

const MempoolLatencyStats = () => {
  const [mempoolData, setMempoolData] = useState<any>(null);
  const [selectedView, setSelectedView] = useState<'btc' | 'usd' | 'both'>(
    'both'
  );

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');

    ws.onopen = () => {
      console.log('[WebSocket] Connected');
    };

    ws.onmessage = (event) => {
      const msg = JSON.parse(event.data);
      if (msg.type === 'mempool_update') {
        setMempoolData(msg.data);
      }
    };

    ws.onerror = (err) => {
      console.error('[WebSocket] Error:', err);
    };

    ws.onclose = () => {
      console.log('[WebSocket] Disconnected');
    };

    return () => {
      ws.close();
    };
  }, []);

  if (!mempoolData) {
    return (
      <div className="text-center text-gray-400 py-10">
        Loading Mempool Stats...
      </div>
    );
  }

  const fees = mempoolData?.fees || {};
  const next = mempoolData?.next_block_fees || {};
  const feeDist = mempoolData?.fee_distribution || {};
  const block_fee_history = mempoolData?.block_fee_history || [];

  const feeDistChartData = Object.entries(feeDist).map(([label, value]) => ({
    name: label,
    value: value || 0,
  }));

  const blockFeeChartData = block_fee_history.map((item: any) => ({
    time: item.time || item.timestamp,
    btc: isNaN(item.btc) ? 0 : item.btc,
    usd: isNaN(item.usd) ? 0 : item.usd,
  }));

  return (
    <div className="flex flex-col gap-8 p-6 text-gray-100">
      {/* --- Overview --- */}
      <section className="rounded-xl p-3 shadow-sm">
        <div className="grid sm:grid-cols-1 md:grid-cols-4 gap-4 mb-6">
          <AnimatedStatCard
            title="Size (vB)"
            value={mempoolData?.mempool?.vsize || '--'}
          />
          <AnimatedStatCard
            title="Transactions"
            value={mempoolData?.mempool?.count || '--'}
          />
          <AnimatedStatCard
            title="Total Fees (BTC | USD)"
            value={`${Number(mempoolData?.mempool?.total_fee_btc).toFixed(6)} BTC | $${Number(
              mempoolData?.mempool?.total_fee_usd
            ).toFixed(2)}`}
          />
          <AnimatedStatCard
            title="Next Block Fees"
            value={`${next?.sats_per_vbyte || '--'} sats/vB | $${Number(
              next?.fee_usd
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
        <div className="shadow p-6">
          <h3 className="text-lg font-semibold text-center mb-4">
            {' '}
            Live Fee Rate Distribution
          </h3>
          <div className="h-64">
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
      <section className="shadow p-6">
        <h2 className="text-lg font-semibold text-center mb-4">
          Block Fees Over Time (1 Week)
        </h2>

        {/* Toggle Buttons */}
        <div className="flex justify-center gap-4 mb-4">
          {['btc', 'usd', 'both'].map((view) => (
            <button
              key={view}
              onClick={() => setSelectedView(view as any)}
              className={`px-4 py-1 rounded-full text-sm ${
                selectedView === view
                  ? 'bg-blue-600 text-white'
                  : 'bg-gray-700 text-gray-300 hover:bg-gray-600'
              }`}
            >
              {view.toUpperCase()}
            </button>
          ))}
        </div>

        <ResponsiveContainer width="100%" height={300}>
          <LineChart data={blockFeeChartData}>
            <CartesianGrid strokeDasharray="3 3" stroke="#374151" />
            <XAxis dataKey="time" stroke="#9ca3af" />
            <YAxis
              yAxisId="left"
              stroke="#9ca3af"
              label={{
                value: 'BTC',
                angle: -90,
                position: 'insideLeft',
                fill: '#9ca3af',
              }}
            />
            <YAxis
              yAxisId="right"
              orientation="right"
              stroke="#9ca3af"
              label={{
                value: 'USD',
                angle: -90,
                position: 'insideRight',
                fill: '#9ca3af',
              }}
            />
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
            <Legend />
            {(selectedView === 'btc' || selectedView === 'both') && (
              <Line
                yAxisId="left"
                type="monotone"
                dataKey="btc"
                stroke="#4ade80"
                dot={false}
                name="BTC"
              />
            )}
            {(selectedView === 'usd' || selectedView === 'both') && (
              <Line
                yAxisId="right"
                type="monotone"
                dataKey="usd"
                stroke={colors.primary}
                dot={false}
                name="USD"
              />
            )}
          </LineChart>
        </ResponsiveContainer>
      </section>
    </div>
  );
};

export default MempoolLatencyStats;
