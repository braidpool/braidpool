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
  visible?: boolean;
  dot?: boolean | object;
};

type MultiLineChartProps = {
  data: unknown[];
  xAxisKey: string;
  series: Series[];
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
};

const MultiLineChart = ({
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
  showLegend = true,
}: MultiLineChartProps) => {
  const visibleSeries = series.filter((item) => item.visible !== false);

  return (
    <ChartFrame
      title={title}
      description={description}
      headerRight={headerRight}
      downloadFileName={downloadFileName}
      height={height}
    >
      <ResponsiveContainer width="100%" height="100%">
        <RechartsLineChart data={data}>
          <CartesianGrid strokeDasharray="3 3" stroke="#374151" />
          <XAxis dataKey={xAxisKey} tickFormatter={xAxisTickFormatter} />
          <YAxis tickFormatter={yAxisTickFormatter} />
          <Tooltip
            contentStyle={{
              backgroundColor: '#1f2937',
              borderRadius: '8px',
              border: 'none',
              color: '#ffffff',
              padding: '15px',
              fontSize: '14px',
            }}
            labelFormatter={tooltipLabelFormatter}
            formatter={(value, name) => [
              tooltipValueFormatter
                ? tooltipValueFormatter(value, String(name))
                : value,
              visibleSeries.find((item) => item.dataKey === name)?.label ?? name,
            ]}
          />
          {showLegend && <Legend />}
          {visibleSeries.map((item) => (
            <Line
              key={item.dataKey}
              type="monotone"
              dataKey={item.dataKey}
              stroke={item.color}
              strokeWidth={2}
              dot={item.dot ?? false}
              name={item.label}
            />
          ))}
        </RechartsLineChart>
      </ResponsiveContainer>
    </ChartFrame>
  );
};

export default MultiLineChart;
