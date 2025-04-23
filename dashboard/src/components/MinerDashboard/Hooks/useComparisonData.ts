import { useMemo } from 'react';
import { useChartData } from './useChartData';

export function useComparisonData(minerId: string | null, timeRange: string) {
  const baseData = useChartData(timeRange);

  const comparisonData = useMemo(() => {
    if (!minerId) return baseData.data;

    // Create a variation of the base data for comparison
    return baseData.data.map((point) => ({
      ...point,
      value: point.value * (0.7 + Math.random() * 0.6), // 70-130% of original value
    }));
  }, [baseData.data, minerId]);

  return {
    baseData: baseData.data,
    comparisonData,
    isLoading: baseData.isLoading,
  };
}
