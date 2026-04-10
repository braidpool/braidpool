import { useMemo, useState } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
  Legend,
} from 'recharts';
import { AnalyticsChartsProps } from './Types';

const AnalyticsCharts = ({ fleetHistory }: AnalyticsChartsProps) => {
  const [activeView, setActiveView] = useState<
    'hashrate' | 'efficiency' | 'temperature'
  >('hashrate');

  const chartConfig = useMemo(() => {
    switch (activeView) {
      case 'efficiency':
        return {
          title: 'Total Average Efficiency (W/TH)',
          lines: [{ key: 'efficiency', color: '#f59e0b', label: 'Efficiency' }],
        };
      case 'temperature':
        return {
          title: 'Total Average Temps (°C)',
          lines: [
            { key: 'temperature', color: '#ef4444', label: 'ASIC' },
            { key: 'vrTemperature', color: '#eab308', label: 'VR' },
          ],
        };
      case 'hashrate':
      default:
        return {
          title: 'Hashrate vs Expected (TH/s)',
          lines: [
            { key: 'totalHashrate', color: '#60a5fa', label: 'Total' },
            { key: 'expectedHashrate', color: '#22c55e', label: 'Expected' },
          ],
        };
    }
  }, [activeView]);

  return (
    <div className="min-h-[350px] mt-9 mb-9">
      <div className="border border-gray-800/50 rounded-xl p-4  backdrop-blur-md overflow-hidden">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-3">
          <div className="text-sm text-gray-300">{chartConfig.title}</div>
          <div className="flex items-center gap-2 text-xs">
            <button
              type="button"
              onClick={() => setActiveView('hashrate')}
              className={`px-3 py-1 rounded border transition cursor-pointer ${
                activeView === 'hashrate'
                  ? ' text-white bg-gray-800 hover:bg-gray-700'
                  : 'border-gray-600 text-gray-400'
              }`}
            >
              Hashrate
            </button>
            <button
              type="button"
              onClick={() => setActiveView('efficiency')}
              className={`px-3 py-1 rounded border transition cursor-pointer ${
                activeView === 'efficiency'
                  ? ' text-white bg-gray-800 hover:bg-gray-700 '
                  : 'border-gray-600 text-gray-400'
              }`}
            >
              Efficiency
            </button>
            <button
              type="button"
              onClick={() => setActiveView('temperature')}
              className={`px-3 py-1 rounded border transition cursor-pointer ${
                activeView === 'temperature'
                  ? ' text-white bg-gray-800 hover:bg-gray-700 '
                  : 'border-gray-600 text-gray-400'
              }`}
            >
              Temps
            </button>
          </div>
        </div>

        {fleetHistory.length === 0 ? (
          <div className="text-xs text-gray-500">
            No analytics yet. Add a miner or refresh.
          </div>
        ) : (
          <ResponsiveContainer width="100%" height={260}>
            <LineChart data={fleetHistory}>
              <CartesianGrid stroke="#444" />
              <XAxis
                dataKey="timestamp"
                tickFormatter={(ts) => new Date(ts).toLocaleTimeString()}
                tick={{ fill: '#aaa' }}
              />
              <YAxis tick={{ fill: '#aaa' }} />
              <Tooltip
                content={({ active, payload, label }) => {
                  if (!active || !payload?.length) return null;
                  return (
                    <div className="bg-[#1e1e1e] border border-gray-700 rounded-lg px-4 py-3 shadow-lg">
                      <div className="text-gray-400 text-sm mb-2">
                        {new Date(label as number).toLocaleTimeString()}
                      </div>
                      {payload.map((entry) => (
                        <div
                          key={entry.dataKey}
                          className="flex items-center gap-2 text-base"
                        >
                          <span
                            className="w-2.5 h-2.5 rounded-full"
                            style={{ backgroundColor: entry.color }}
                          />
                          <span className="text-gray-300">{entry.name}:</span>
                          <span className="text-white font-medium">
                            {typeof entry.value === 'number'
                              ? entry.value.toFixed(2)
                              : entry.value}
                          </span>
                        </div>
                      ))}
                    </div>
                  );
                }}
              />
              <Legend />
              {chartConfig.lines.map((line) => (
                <Line
                  key={line.key}
                  type="monotone"
                  dataKey={line.key}
                  stroke={line.color}
                  dot={false}
                  name={line.label}
                />
              ))}
            </LineChart>
          </ResponsiveContainer>
        )}
      </div>
    </div>
  );
};

export default AnalyticsCharts;
