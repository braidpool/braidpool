import {
  CartesianGrid,
  Legend,
  Line,
  LineChart as RechartsLineChart,
  ResponsiveContainer,
  Tooltip,
  XAxis,
  YAxis,
} from 'recharts';
import ChartFrame from './ChartFrame';

type Series = {
  dataKey: string;
  label: string;
  color: string;
  yAxisId?: string | number;
};

type TwoLineChartProps = {
  data: unknown[];
  xAxisKey: string;
  series: [Series, Series];
  title?: React.ReactNode;
  description?: React.ReactNode;
  headerRight?: React.ReactNode;
  downloadFileName?: string;
  height?: number;
  xAxisTickFormatter?: (value: unknown) => string;
  yAxisTickFormatter?: (value: number) => string;
  tooltipLabelFormatter?: (value: unknown) => string;
  tooltipValueFormatter?: (value: unknown, dataKey: string) => string;
  showLegend?: boolean;
  dualAxis?: boolean;
};

const TwoLineChart = ({
  data,
  xAxisKey,
  series,
  title,
  description,
  headerRight,
  downloadFileName,
  height = 350,
  xAxisTickFormatter,
  yAxisTickFormatter,
  tooltipLabelFormatter,
  tooltipValueFormatter,
  showLegend = false,
  dualAxis = false,
}: TwoLineChartProps) => (
  <ChartFrame
    title={title}
    description={description}
    headerRight={headerRight}
    downloadFileName={downloadFileName}
    height={height}
  >
    <ResponsiveContainer width="100%" height="100%">
      <RechartsLineChart data={data}>
        <CartesianGrid strokeDasharray="3 3" stroke="#444" />
        <XAxis dataKey={xAxisKey} tickFormatter={xAxisTickFormatter} />
        <YAxis yAxisId="left" tickFormatter={yAxisTickFormatter} />
        {dualAxis && <YAxis yAxisId="right" orientation="right" />}
        <Tooltip
          contentStyle={{ backgroundColor: '#2d2d2d', borderColor: '#555' }}
          labelFormatter={tooltipLabelFormatter}
          formatter={(value, name) => [
            tooltipValueFormatter
              ? tooltipValueFormatter(value, String(name))
              : value,
            series.find((item) => item.dataKey === name)?.label ?? name,
          ]}
        />
        {showLegend && <Legend />}
        {series.map((item) => (
          <Line
            key={item.dataKey}
            type="monotone"
            dataKey={item.dataKey}
            name={item.label}
            stroke={item.color}
            yAxisId={item.yAxisId ?? 'left'}
            dot={false}
          />
        ))}
      </RechartsLineChart>
    </ResponsiveContainer>
  </ChartFrame>
);

export default TwoLineChart;
