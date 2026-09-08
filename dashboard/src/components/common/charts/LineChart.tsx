import {
  CartesianGrid,
  Line,
  LineChart as RechartsLineChart,
  ResponsiveContainer,
  Tooltip,
  XAxis,
  YAxis,
} from 'recharts';
import ChartFrame from './ChartFrame';

type LineChartProps = {
  data: unknown[];
  xAxisKey: string;
  dataKey: string;
  label?: string;
  color?: string;
  unit?: string;
  title?: React.ReactNode;
  description?: React.ReactNode;
  headerRight?: React.ReactNode;
  downloadFileName?: string;
  height?: number;
  xAxisType?: 'category' | 'number';
  xAxisScale?: any;
  xAxisDomain?: [string, string];
  xAxisTickFormatter?: (value: unknown) => string;
  yAxisTickFormatter?: (value: number) => string;
  tooltipLabelFormatter?: (value: unknown) => string;
  tooltipValueFormatter?: (value: unknown) => string;
};

const LineChart = ({
  data,
  xAxisKey,
  dataKey,
  label,
  color = '#3b82f6',
  unit,
  title,
  description,
  headerRight,
  downloadFileName,
  height = 350,
  xAxisType = 'category',
  xAxisScale,
  xAxisDomain,
  xAxisTickFormatter,
  yAxisTickFormatter,
  tooltipLabelFormatter,
  tooltipValueFormatter,
}: LineChartProps) => (
  <ChartFrame
    title={title}
    description={description}
    headerRight={headerRight}
    downloadFileName={downloadFileName}
    height={height}
  >
    <ResponsiveContainer width="100%" height="100%">
      <RechartsLineChart data={data}>
        <CartesianGrid stroke="#444" />
        <XAxis
          dataKey={xAxisKey}
          type={xAxisType}
          scale={xAxisScale as any}
          domain={xAxisDomain}
          tickFormatter={xAxisTickFormatter}
          tick={{ fill: '#aaa' }}
        />
        <YAxis
          unit={unit ? ` ${unit}` : undefined}
          tickFormatter={yAxisTickFormatter}
          tick={{ fill: '#aaa' }}
        />
        <Tooltip
          contentStyle={{ backgroundColor: '#2d2d2d', borderColor: '#555' }}
          labelFormatter={tooltipLabelFormatter}
          formatter={(value) => [
            tooltipValueFormatter
              ? tooltipValueFormatter(value)
              : `${value}${unit ? ` ${unit}` : ''}`,
            label ?? dataKey,
          ]}
        />
        <Line
          type="monotone"
          dataKey={dataKey}
          name={label ?? dataKey}
          stroke={color}
          strokeWidth={2}
          dot={false}
        />
      </RechartsLineChart>
    </ResponsiveContainer>
  </ChartFrame>
);

export default LineChart;
