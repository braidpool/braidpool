import { AdvancedchartProps } from './lib/Types';
import MultiLineChart from '../common/charts/MultiLineChart';

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
  return (
    <MultiLineChart
      data={data}
      xAxisKey="timestamp"
      series={[{ dataKey: 'value', label: yLabel ?? 'Value', color: lineColor }]}
      unit={unit}
      title={title}
      description={description}
      headerRight={headerRight}
      downloadFileName={downloadFileName}
      xAxisType="number"
      xAxisScale="time"
      xAxisDomain={['auto', 'auto']}
      xAxisTickFormatter={(timestamp) =>
        new Date(Number(timestamp)).toLocaleTimeString([], {
          hour: '2-digit',
          minute: '2-digit',
          second: '2-digit',
        })
      }
      tooltipLabelFormatter={(timestamp) =>
        new Date(Number(timestamp)).toLocaleTimeString([], {
          hour: '2-digit',
          minute: '2-digit',
          second: '2-digit',
        })
      }
      tooltipValueFormatter={(value) => `${Number(value).toFixed(2)} ${unit}`}
    />
  );
}
