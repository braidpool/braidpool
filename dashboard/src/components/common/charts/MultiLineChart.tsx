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
import type { MultiLineChartProps } from './Type';


const MultiLineChart = ({
  data,
  xAxisKey,
  series,
  title,
  description,
  headerRight,
  downloadFileName,
  height = 350,
  unit,
  xAxisType = 'category',
  xAxisScale,
  xAxisDomain,
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
          <CartesianGrid strokeDasharray="3 3" stroke="#444" />
          <XAxis
            dataKey={xAxisKey}
            type={xAxisType}
            scale={xAxisScale as any}
            domain={xAxisDomain}
            tickFormatter={xAxisTickFormatter}
          />
          <YAxis
            yAxisId="left"
            unit={unit ? ` ${unit}` : undefined}
            tickFormatter={yAxisTickFormatter}
          />
          {visibleSeries.some((item) => item.yAxisId === 'right') && (
            <YAxis yAxisId="right" orientation="right" />
          )}
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
                : `${value}${unit ? ` ${unit}` : ''}`,
              visibleSeries.find((item) => item.dataKey === name)?.label ??
                name ??
                visibleSeries[0]?.label,
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
              yAxisId={item.yAxisId ?? 'left'}
            />
          ))}
        </RechartsLineChart>
      </ResponsiveContainer>
    </ChartFrame>
  );
};

export default MultiLineChart;
