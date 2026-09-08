import {
  Bar,
  BarChart as RechartsBarChart,
  CartesianGrid,
  Legend,
  ResponsiveContainer,
  Tooltip,
  XAxis,
  YAxis,
} from 'recharts';
import ChartFrame from './ChartFrame';

type BarChartProps = {
  data: unknown[];
  xAxisKey: string;
  dataKey: string;
  label?: string;
  color?: string;
  title?: React.ReactNode;
  description?: React.ReactNode;
  headerRight?: React.ReactNode;
  downloadFileName?: string;
  height?: number;
  yAxisTickFormatter?: (value: number) => string;
  tooltipValueFormatter?: (value: unknown) => string;
};

const BarChart = ({
  data,
  xAxisKey,
  dataKey,
  label,
  color = '#3b82f6',
  title,
  description,
  headerRight,
  downloadFileName,
  height = 320,
  yAxisTickFormatter,
  tooltipValueFormatter,
}: BarChartProps) => (
  <ChartFrame
    title={title}
    description={description}
    headerRight={headerRight}
    downloadFileName={downloadFileName}
    height={height}
  >
    <ResponsiveContainer width="100%" height="100%">
      <RechartsBarChart data={data}>
        <CartesianGrid strokeDasharray="3 3" />
        <XAxis dataKey={xAxisKey} />
        <YAxis tickFormatter={yAxisTickFormatter} />
        <Tooltip
          formatter={(value) => [
            tooltipValueFormatter ? tooltipValueFormatter(value) : value,
            label ?? dataKey,
          ]}
        />
        <Legend />
        <Bar dataKey={dataKey} name={label ?? dataKey} fill={color} />
      </RechartsBarChart>
    </ResponsiveContainer>
  </ChartFrame>
);

export default BarChart;
