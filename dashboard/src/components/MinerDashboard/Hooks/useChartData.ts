import { useState, useEffect } from "react"
import { TIME_RANGES } from "../constants"
import type { ChartDataPoint } from "../types"

export function useChartData(timeRange: string) {
  const [data, setData] = useState<ChartDataPoint[]>([])
  const [isLoading, setIsLoading] = useState(true)
  const [dateRange, setDateRange] = useState({ start: "", end: "" })

  useEffect(() => {
    setIsLoading(true)
    const selectedRange = TIME_RANGES.find((range) => range.value === timeRange) || TIME_RANGES[1]
    const endDate = new Date()
    const startDate = new Date()
    startDate.setDate(endDate.getDate() - selectedRange.days)
    setDateRange({
      start: startDate.toLocaleDateString("en-US", { year: "numeric", month: "short", day: "numeric" }),
      end: endDate.toLocaleDateString("en-US", { year: "numeric", month: "short", day: "numeric" }),
    })

    let interval = 1
    let format = "day"
    if (timeRange === "week") interval = 1
    else if (timeRange === "month") interval = 3
    else if (timeRange === "quarter") { interval = 7; format = "week" }
    else if (timeRange === "year") { interval = 30; format = "month" }

    const dataPoints: ChartDataPoint[] = []
    const currentDate = new Date(startDate)
    while (currentDate <= endDate) {
      const value = Math.floor(Math.random() * 100) + 50
      let label = ""
      if (format === "day") label = currentDate.toLocaleDateString("en-US", { month: "short", day: "numeric" })
      else if (format === "week") label = currentDate.toLocaleDateString("en-US", { month: "short", day: "numeric" })
      else if (format === "month") label = currentDate.toLocaleDateString("en-US", { month: "short", year: "2-digit" })
      dataPoints.push({
        value,
        label,
        date: new Date(currentDate),
        formattedDate: currentDate.toLocaleDateString("en-US", {
          year: "numeric",
          month: "short",
          day: "numeric",
          weekday: "short",
        }),
        trend: dataPoints.length > 0 ? (value > dataPoints[dataPoints.length - 1].value ? "up" : "down") : "neutral",
      })
      currentDate.setDate(currentDate.getDate() + interval)
    }
    setTimeout(() => {
      setData(dataPoints)
      setIsLoading(false)
    }, 500)
  }, [timeRange])

  return { data, isLoading, dateRange }
}