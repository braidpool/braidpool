import React from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
} from 'recharts';

import { AdvancedchartProps } from './lib/Types';

export default function AdvancedChart({
  data,
  yLabel,
  unit,
  lineColor = '#3b82f6',
}: AdvancedchartProps) {
  return (
    <div className=" relative border border-gray-800/50 rounded-xl p-4 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden  ">
      <ResponsiveContainer width="100%" height={350}>
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
  );
}
