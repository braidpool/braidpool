import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
} from 'recharts';
import { useRef } from 'react';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';
import { Download } from 'lucide-react';

import { AdvancedchartProps } from './lib/Types';

const CHART_HEIGHT = 350;

export default function AdvancedChart({
  data,
  yLabel,
  unit,
  lineColor = '#3b82f6',
  title,
  description,
  headerRight,
  downloadFileName = 'advanced-chart',
}: AdvancedchartProps) {
  const chartContainerRef = useRef<HTMLDivElement | null>(null);

  const handleDownload = () => {
    if (!chartContainerRef.current) return;
    downloadSvgFromContainer(chartContainerRef.current, downloadFileName);
  };

  return (
    <div
      className="relative border border-gray-800/50 rounded-xl p-4 w-full backdrop-blur-md overflow-hidden"
      style={{ minHeight: title ? CHART_HEIGHT + 48 : CHART_HEIGHT }}
    >
      {title && (
        <div className="flex items-start justify-between mb-4">
          <div className="flex flex-col">
            <div className="flex items-center gap-2">
              <h3 className="text-xl font-bold text-blue-300">{title}</h3>
              <button
                onClick={handleDownload}
                className="p-1.5 rounded text-gray-500 hover:text-gray-300 hover:bg-gray-800 transition-colors"
                aria-label="Download chart"
              >
                <Download className="w-4 h-4" />
              </button>
            </div>
            {description && (
              <div className="text-sm text-gray-400 mt-1">{description}</div>
            )}
          </div>
          {headerRight && <div>{headerRight}</div>}
        </div>
      )}
      <div
        ref={chartContainerRef}
        style={{ width: '100%', height: CHART_HEIGHT }}
      >
        <ResponsiveContainer width="100%" height="100%">
          <LineChart data={data}>
            <CartesianGrid stroke="#444" />
            <XAxis
              className="text-sm"
              dataKey="timestamp"
              domain={['auto', 'auto']}
              type="number"
              scale="time"
              tickFormatter={(ts) =>
                new Date(ts).toLocaleTimeString([], {
                  hour: '2-digit',
                  minute: '2-digit',
                  second: '2-digit',
                })
              }
              tick={{ fill: '#aaa' }}
            />
            <YAxis
              className="text-sm"
              tick={{ fill: '#aaa' }}
              unit={` ${unit}`}
            />
            <Tooltip
              contentStyle={{
                backgroundColor: '#2d2d2d',
                borderColor: '#555',
              }}
              labelFormatter={(ts) =>
                new Date(ts).toLocaleTimeString([], {
                  hour: '2-digit',
                  minute: '2-digit',
                  second: '2-digit',
                })
              }
              formatter={(value: number) => [
                `${value.toFixed(2)} ${unit}`,
                yLabel,
              ]}
            />
            <Line
              type="monotone"
              dataKey="value"
              stroke={lineColor}
              strokeWidth={2}
              dot={false}
            />
          </LineChart>
        </ResponsiveContainer>
      </div>
    </div>
  );
}
