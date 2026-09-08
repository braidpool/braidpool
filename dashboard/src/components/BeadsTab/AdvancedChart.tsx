import { AdvancedchartProps } from './lib/Types';
import LineChart from '../common/charts/LineChart';

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
    <LineChart
      data={data}
      xAxisKey="timestamp"
      dataKey="value"
      label={yLabel}
      color={lineColor}
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
