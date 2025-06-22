import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';

export default function TransactionsTab({
  chartData,
  isChartLoading,
  chartHovered,
  setChartHovered,
  timeRange,
  stats,
}: any) {
  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">
            Transaction Activity
          </h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time transaction statistics
          </p>
        </div>
        <div className="bg-emerald-900/30 px-3 py-1 rounded-md">
          <span className="text-emerald-300 font-mono">
            {stats?.txRate ? `${stats.txRate.toFixed(1)} tx/min` : 'Loading...'}
          </span>
        </div>
      </div>

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData}
          height={350}
          isHovered={chartHovered}
          isLoading={isChartLoading}
          timeRange={timeRange}
          primaryLabel="Transactions per Block"
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 gap-6">
        <AnimatedStatCard
          title="Mempool Size"
          value={stats?.mempoolSize ? `${stats.mempoolSize} tx` : 'Loading...'}
        />
        <AnimatedStatCard
          title="Avg Fee Rate"
          value={
            stats?.avgFeeRate
              ? `${stats.avgFeeRate.toFixed(1)} sats/vB`
              : 'Loading...'
          }
        />
        <AnimatedStatCard
          title="Avg Tx Size"
          value={stats?.avgTxSize ? `${stats.avgTxSize} vB` : 'Loading...'}
        />
      </div>
    </div>
  );
}
