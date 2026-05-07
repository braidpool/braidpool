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
import ActionIconButton from '../common/ActionIconButton';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';

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
              <ActionIconButton
                onClick={handleDownload}
                ariaLabel="Download chart"
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
