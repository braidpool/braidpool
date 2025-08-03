import Card from '../common/Card';
import colors from '../../theme/colors';
import { CHART_Y_OFFSET, CHART_Y_SCALE } from './Constants';

// Mock data for latency stats
const latencyData = [
  { time: '5m', value: 215 },
  { time: '10m', value: 223 },
  { time: '15m', value: 198 },
  { time: '20m', value: 205 },
  { time: '25m', value: 231 },
  { time: '30m', value: 227 },
  { time: '35m', value: 212 },
  { time: '40m', value: 219 },
  { time: '45m', value: 208 },
  { time: '50m', value: 201 },
  { time: '55m', value: 197 },
  { time: '60m', value: 203 },
];

// Mock data for mempool stats
const mempoolData = {
  size: '183.7 MB',
  txCount: '12,487',
  nextBlockFees: '0.00042 BTC',
  feeRates: {
    high: '21 sat/vB',
    medium: '14 sat/vB',
    low: '8 sat/vB',
  },
  feeEstimates: {
    fastest: '~10 min',
    fast: '~30 min',
    standard: '~1 hour',
    economy: '~3 hours',
  },
};

const StatItem = ({
  label,
  value,
  color,
}: {
  label: string;
  value: string;
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

const FeeRate = ({
  level,
  rate,
  time,
}: {
  level: string;
  rate: string;
  time: string;
}) => (
  <div className="flex justify-between mb-3">
    <div className="flex items-center">
      <div
        className="w-2 h-2 rounded-full mr-3"
        style={{
          backgroundColor:
            level === 'Fastest'
              ? colors.error
              : level === 'Fast'
                ? colors.warning
                : level === 'Standard'
                  ? colors.success
                  : colors.textSecondary,
        }}
      />
      <span className="text-sm">{level}</span>
    </div>
    <span className="text-sm" style={{ color: colors.textSecondary }}>
      {rate}
    </span>
    <span className="text-sm" style={{ color: colors.textSecondary }}>
      {time}
    </span>
  </div>
);

const MempoolLatencyStats = () => {
  return (
    <Card
      title="Network Performance"
      subtitle="Mempool stats and latency metrics"
      accentColor={colors.cardAccentPrimary}
    >
      <div className="flex flex-col md:flex-row gap-6">
        {/* Mempool Stats */}
        <div className="flex-1">
          <div
            className="p-4 rounded h-full"
            style={{
              backgroundColor: colors.paper,
              border: `1px solid ${colors.primary}20`,
            }}
          >
            <h6 className="mb-4 font-medium text-lg">Mempool Status</h6>

            <div className="grid grid-cols-2 gap-4 mb-4">
              <StatItem label="SIZE" value={mempoolData.size} />
              <StatItem label="TRANSACTIONS" value={mempoolData.txCount} />
              <StatItem
                label="NEXT BLOCK FEES"
                value={mempoolData.nextBlockFees}
                color={colors.secondary}
              />
              <StatItem
                label="HIGH PRIORITY FEE"
                value={mempoolData.feeRates.high}
                color={colors.error}
              />
            </div>

            <hr className="my-4" style={{ borderColor: colors.primary }} />

            <h6 className="mb-4 font-medium text-sm">Fee Estimates</h6>

            <FeeRate
              level="Fastest"
              rate={mempoolData.feeRates.high}
              time={mempoolData.feeEstimates.fastest}
            />
            <FeeRate
              level="Fast"
              rate={mempoolData.feeRates.medium}
              time={mempoolData.feeEstimates.fast}
            />
            <FeeRate
              level="Standard"
              rate={mempoolData.feeRates.medium}
              time={mempoolData.feeEstimates.standard}
            />
            <FeeRate
              level="Economy"
              rate={mempoolData.feeRates.low}
              time={mempoolData.feeEstimates.economy}
            />
          </div>
        </div>

        {/* Latency Stats */}
        <div className="flex-1">
          <div
            className="p-4 rounded h-full"
            style={{
              backgroundColor: colors.paper,
              border: `1px solid ${colors.primary}20`,
            }}
          >
            <h6 className="mb-4 font-medium text-lg">Network Latency</h6>

            <div className="mb-4">
              <div className="flex justify-between">
                <span
                  className="text-xs"
                  style={{ color: colors.textSecondary }}
                >
                  Current:{' '}
                  <span
                    className="font-medium"
                    style={{ color: colors.textPrimary }}
                  >
                    203 ms
                  </span>
                </span>
                <span
                  className="text-xs"
                  style={{ color: colors.textSecondary }}
                >
                  Avg (1h):{' '}
                  <span
                    className="font-medium"
                    style={{ color: colors.textPrimary }}
                  >
                    211 ms
                  </span>
                </span>
                <span
                  className="text-xs"
                  style={{ color: colors.textSecondary }}
                >
                  Best:{' '}
                  <span
                    className="font-medium"
                    style={{ color: colors.success }}
                  >
                    197 ms
                  </span>
                </span>
              </div>
            </div>

            {/* Latency Chart */}
            <div className="relative h-48 mt-6">
              <div
                className="absolute inset-0"
                style={{
                  backgroundImage: `linear-gradient(to right, ${colors.chartGrid} 1px, transparent 1px), 
                                  linear-gradient(to bottom, ${colors.chartGrid} 1px, transparent 1px)`,
                  backgroundSize: '20% 25%',
                  opacity: 0.2,
                }}
              />

              <svg className="w-full h-full">
                <path
                  d={`M 0,${CHART_Y_OFFSET - ((latencyData[0].value - 190) / CHART_Y_SCALE) * 100} 
                    ${latencyData
                      .map((point, i) => {
                        const x = i * (100 / (latencyData.length - 1));
                        const y =
                          CHART_Y_OFFSET -
                          ((point.value - 190) / CHART_Y_SCALE) * 100;
                        return `L ${x},${y}`;
                      })
                      .join(' ')}`}
                  fill="none"
                  stroke={colors.primary}
                  strokeWidth="2"
                />
                {latencyData.map((point, i) => {
                  const x = i * (100 / (latencyData.length - 1));
                  const y =
                    CHART_Y_OFFSET -
                    ((point.value - 190) / CHART_Y_SCALE) * 100;
                  return (
                    <circle
                      key={i}
                      cx={`${x}%`}
                      cy={`${y}%`}
                      r="3"
                      fill={colors.primary}
                      stroke={colors.chartBackground}
                      strokeWidth="1"
                    />
                  );
                })}
              </svg>

              {/* Y-axis labels */}
              <div className="absolute top-0 bottom-0 left-0 flex flex-col justify-between pr-2">
                <span
                  className="text-[0.7rem]"
                  style={{ color: colors.textSecondary }}
                >
                  240ms
                </span>
                <span
                  className="text-[0.7rem]"
                  style={{ color: colors.textSecondary }}
                >
                  215ms
                </span>
                <span
                  className="text-[0.7rem]"
                  style={{ color: colors.textSecondary }}
                >
                  190ms
                </span>
              </div>

              {/* X-axis labels */}
              <div className="absolute bottom-[-20px] left-0 right-0 flex justify-between">
                <span
                  className="text-[0.7rem]"
                  style={{ color: colors.textSecondary }}
                >
                  60m
                </span>
                <span
                  className="text-[0.7rem]"
                  style={{ color: colors.textSecondary }}
                >
                  30m
                </span>
                <span
                  className="text-[0.7rem]"
                  style={{ color: colors.textSecondary }}
                >
                  5m
                </span>
              </div>
            </div>

            <hr className="my-4" style={{ borderColor: colors.primary }} />

            <div className="flex justify-between">
              <StatItem label="SWITCHING TIME" value="1.8s" />
              <StatItem label="LAMBDA" value="1.87" />
              <StatItem label="A PARAMETER" value="3.2" />
            </div>
          </div>
        </div>
      </div>
    </Card>
  );
};

export default MempoolLatencyStats;
