import type { ReactNode } from 'react';
export type BarChartProps = {
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
export type ChartFrameProps = {
  children: ReactNode;
  title?: ReactNode;
  description?: ReactNode;
  headerRight?: ReactNode;
  downloadFileName?: string;
  className?: string;
  height?: number;
};
export type Series = {
  dataKey: string;
  label: string;
  color: string;
  visible?: boolean;
  dot?: boolean | object;
  yAxisId?: string | number;
};

export type MultiLineChartProps = {
  data: unknown[];
  xAxisKey: string;
  series: Series[];
  title?: React.ReactNode;
  description?: React.ReactNode;
  headerRight?: React.ReactNode;
  downloadFileName?: string;
  height?: number;
  unit?: string;
  xAxisType?: 'category' | 'number';
  xAxisScale?: string;
  xAxisDomain?: [string | number, string | number];
  xAxisTickFormatter?: (value: unknown) => string;
  yAxisTickFormatter?: (value: number) => string;
  tooltipLabelFormatter?: (value: unknown) => string;
  tooltipValueFormatter?: (value: unknown, dataKey: string) => string;
  showLegend?: boolean;
};
