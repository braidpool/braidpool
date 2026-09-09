import { useEffect, useState, useRef } from 'react';
import colors from '../../theme/colors';
import AnimatedStatCard from '../BeadsTab/AnimatedStatCard';
import {
  Fee,
  BlockFeeHistoryItem,
  MempoolData,
  FeeDistributionItem,
} from './Types';
import { currencyColors } from './Constants';
import { WEBSOCKET_URLS } from '@/URLs';
import { Loader } from 'lucide-react';
import UnifiedBarChart from '../common/charts/BarChart';
import MultiLineChart from '../common/charts/MultiLineChart';

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
          <UnifiedBarChart
            data={feeDistChartData}
            xAxisKey="name"
            dataKey="value"
            label="Fee rate"
            color={colors.primary}
            title="Live Fee Rate Distribution"
            downloadFileName="mempool-fee-distribution"
            height={256}
          />
        </div>
      </section>

      {/* --- Block Fee Chart --- */}
      <section className="shadow p-6 relative">
        <MultiLineChart
          data={blockFeeChartData}
          xAxisKey="time"
          title="Live Block Fees"
          headerRight={
            <select
              value={selectedView}
              onChange={(e) =>
                setSelectedView(e.target.value as typeof selectedView)
              }
              className="px-4 py-2 bg-[#1a1a1a] text-gray-300 rounded-md shadow-md border border-white"
            >
              {(['btc', 'usd', 'eur', 'jpy', 'all'] as const).map((view) => (
                <option key={view} value={view}>
                  {view.toUpperCase()}
                </option>
              ))}
            </select>
          }
          series={[
            {
              dataKey: 'btc',
              label: 'BTC',
              color: currencyColors.btc,
              visible: selectedView === 'btc' || selectedView === 'all',
              dot: { r: 4 },
            },
            {
              dataKey: 'usd',
              label: 'USD',
              color: currencyColors.usd,
              visible: selectedView === 'usd' || selectedView === 'all',
              dot: { r: 4 },
            },
            {
              dataKey: 'eur',
              label: 'EUR',
              color: currencyColors.eur,
              visible: selectedView === 'eur' || selectedView === 'all',
              dot: { r: 4 },
            },
            {
              dataKey: 'jpy',
              label: 'JPY',
              color: currencyColors.jpy,
              visible: selectedView === 'jpy' || selectedView === 'all',
              dot: { r: 4 },
            },
          ]}
          downloadFileName="mempool-block-fees"
          height={400}
          tooltipValueFormatter={(value, dataKey) =>
            dataKey === 'btc'
              ? `${Number(value).toFixed(6)} BTC`
              : dataKey === 'jpy'
                ? `¥${Number(value).toFixed(0)}`
                : dataKey === 'eur'
                  ? `€${Number(value).toFixed(2)}`
                  : `${Number(value).toFixed(2)}`
          }
        />
      </section>
    </div>
  );
};

export default MempoolLatencyStats;
