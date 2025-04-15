import { useMemo } from "react"
import { useChartData } from "./useChartData"


export function useComparisonData(minerId: string | null, timeRange: string) {
  const baseData = useChartData(timeRange)
  const comparisonData = useMemo(() => {
    if (!minerId) return baseData.data
    return baseData.data.map((point) => ({
      ...point,
      value: point.value * (0.7 + Math.random() * 0.6),
    }))
  }, [baseData.data, minerId])
  return {
    baseData: baseData.data,
    comparisonData,
    isLoading: baseData.isLoading,
  }
}