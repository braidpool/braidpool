"use client"

import { useEffect, useRef } from "react"
import * as d3 from "d3"
import { Loader2 } from "lucide-react"
import type { TransactionMetricsData } from "@/lib/types"
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs"

interface TransactionMetricsProps {
  data: TransactionMetricsData | null
  isLoading: boolean
}

export default function TransactionMetrics({ data, isLoading }: TransactionMetricsProps) {
  const transactionRateChartRef = useRef<SVGSVGElement>(null)
  const confirmationTimeChartRef = useRef<SVGSVGElement>(null)
  const feeDistributionChartRef = useRef<SVGSVGElement>(null)

  // Render transaction rate chart
  useEffect(() => {
    if (!transactionRateChartRef.current || !data || isLoading) return

    const svg = d3.select(transactionRateChartRef.current)
    svg.selectAll("*").remove()

    const width = 800
    const height = 300
    const margin = { top: 20, right: 30, bottom: 30, left: 50 }
    const innerWidth = width - margin.left - margin.right
    const innerHeight = height - margin.top - margin.bottom

    const container = svg
      .attr("width", width)
      .attr("height", height)
      .append("g")
      .attr("transform", `translate(${margin.left},${margin.top})`)

    // Add dark background
    svg.append("rect").attr("width", width).attr("height", height).attr("fill", "none")

    // Create scales
    const xScale = d3
      .scaleTime()
      .domain(d3.extent(data.transactionRateHistory, (d) => new Date(d.timestamp)) as [Date, Date])
      .range([0, innerWidth])

    const yScale = d3
      .scaleLinear()
      .domain([0, (d3.max(data.transactionRateHistory, (d) => d.value) as number) * 1.1])
      .range([innerHeight, 0])

    // Create line generator
    const line = d3
      .line<{ timestamp: string; value: number }>()
      .x((d) => xScale(new Date(d.timestamp)))
      .y((d) => yScale(d.value))
      .curve(d3.curveMonotoneX)

    // Add axes
    container
      .append("g")
      .attr("transform", `translate(0,${innerHeight})`)
      .call(d3.axisBottom(xScale).ticks(5))
      .attr("color", "#718096")
      .selectAll("text")
      .attr("fill", "#a0aec0")

    container
      .append("g")
      .call(d3.axisLeft(yScale).ticks(5))
      .attr("color", "#718096")
      .selectAll("text")
      .attr("fill", "#a0aec0")

    // Add grid lines
    container
      .append("g")
      .attr("class", "grid")
      .selectAll("line")
      .data(yScale.ticks(5))
      .enter()
      .append("line")
      .attr("x1", 0)
      .attr("x2", innerWidth)
      .attr("y1", (d) => yScale(d))
      .attr("y2", (d) => yScale(d))
      .attr("stroke", "#2d3748")
      .attr("stroke-width", 1)

    // Add the line path
    container
      .append("path")
      .datum(data.transactionRateHistory)
      .attr("fill", "none")
      .attr("stroke", "#4299e1")
      .attr("stroke-width", 2)
      .attr("d", line)
      .attr("opacity", 0)
      .transition()
      .duration(1000)
      .attr("opacity", 1)

    // Add area under the line
    const area = d3
      .area<{ timestamp: string; value: number }>()
      .x((d) => xScale(new Date(d.timestamp)))
      .y0(innerHeight)
      .y1((d) => yScale(d.value))
      .curve(d3.curveMonotoneX)

    container
      .append("path")
      .datum(data.transactionRateHistory)
      .attr("fill", "url(#gradient)")
      .attr("d", area)
      .attr("opacity", 0)
      .transition()
      .duration(1000)
      .attr("opacity", 0.3)

    // Add gradient
    const gradient = svg
      .append("defs")
      .append("linearGradient")
      .attr("id", "gradient")
      .attr("x1", "0%")
      .attr("y1", "0%")
      .attr("x2", "0%")
      .attr("y2", "100%")

    gradient.append("stop").attr("offset", "0%").attr("stop-color", "#4299e1").attr("stop-opacity", 0.8)

    gradient.append("stop").attr("offset", "100%").attr("stop-color", "#4299e1").attr("stop-opacity", 0)
  }, [data, isLoading])

  // Render confirmation time chart
  useEffect(() => {
    if (!confirmationTimeChartRef.current || !data || isLoading) return

    const svg = d3.select(confirmationTimeChartRef.current)
    svg.selectAll("*").remove()

    const width = 800
    const height = 300
    const margin = { top: 20, right: 30, bottom: 30, left: 50 }
    const innerWidth = width - margin.left - margin.right
    const innerHeight = height - margin.top - margin.bottom

    const container = svg
      .attr("width", width)
      .attr("height", height)
      .append("g")
      .attr("transform", `translate(${margin.left},${margin.top})`)

    // Add dark background
    svg.append("rect").attr("width", width).attr("height", height).attr("fill", "none")

    // Create scales
    const xScale = d3
      .scaleTime()
      .domain(d3.extent(data.confirmationTimeHistory, (d) => new Date(d.timestamp)) as [Date, Date])
      .range([0, innerWidth])

    const yScale = d3
      .scaleLinear()
      .domain([0, (d3.max(data.confirmationTimeHistory, (d) => d.value) as number) * 1.1])
      .range([innerHeight, 0])

    // Create line generator
    const line = d3
      .line<{ timestamp: string; value: number }>()
      .x((d) => xScale(new Date(d.timestamp)))
      .y((d) => yScale(d.value))
      .curve(d3.curveMonotoneX)

    // Add axes
    container
      .append("g")
      .attr("transform", `translate(0,${innerHeight})`)
      .call(d3.axisBottom(xScale).ticks(5))
      .attr("color", "#718096")
      .selectAll("text")
      .attr("fill", "#a0aec0")

    container
      .append("g")
      .call(d3.axisLeft(yScale).ticks(5))
      .attr("color", "#718096")
      .selectAll("text")
      .attr("fill", "#a0aec0")

    // Add grid lines
    container
      .append("g")
      .attr("class", "grid")
      .selectAll("line")
      .data(yScale.ticks(5))
      .enter()
      .append("line")
      .attr("x1", 0)
      .attr("x2", innerWidth)
      .attr("y1", (d) => yScale(d))
      .attr("y2", (d) => yScale(d))
      .attr("stroke", "#2d3748")
      .attr("stroke-width", 1)

    // Add the line path
    container
      .append("path")
      .datum(data.confirmationTimeHistory)
      .attr("fill", "none")
      .attr("stroke", "#68d391")
      .attr("stroke-width", 2)
      .attr("d", line)
      .attr("opacity", 0)
      .transition()
      .duration(1000)
      .attr("opacity", 1)
  }, [data, isLoading])

  // Render fee distribution chart
  useEffect(() => {
    if (!feeDistributionChartRef.current || !data || isLoading) return

    const svg = d3.select(feeDistributionChartRef.current)
    svg.selectAll("*").remove()

    const width = 800
    const height = 300
    const margin = { top: 20, right: 30, bottom: 50, left: 50 }
    const innerWidth = width - margin.left - margin.right
    const innerHeight = height - margin.top - margin.bottom

    const container = svg
      .attr("width", width)
      .attr("height", height)
      .append("g")
      .attr("transform", `translate(${margin.left},${margin.top})`)

    // Add dark background
    svg.append("rect").attr("width", width).attr("height", height).attr("fill", "none")

    // Create scales
    const xScale = d3
      .scaleBand()
      .domain(data.feeDistribution.map((d) => d.category))
      .range([0, innerWidth])
      .padding(0.3)

    const yScale = d3
      .scaleLinear()
      .domain([0, (d3.max(data.feeDistribution, (d) => d.count) as number) * 1.1])
      .range([innerHeight, 0])

    // Add axes
    container
      .append("g")
      .attr("transform", `translate(0,${innerHeight})`)
      .call(d3.axisBottom(xScale))
      .attr("color", "#718096")
      .selectAll("text")
      .attr("fill", "#a0aec0")
      .attr("transform", "rotate(-45)")
      .attr("text-anchor", "end")
      .attr("dx", "-.8em")
      .attr("dy", ".15em")

    container
      .append("g")
      .call(d3.axisLeft(yScale).ticks(5))
      .attr("color", "#718096")
      .selectAll("text")
      .attr("fill", "#a0aec0")

    // Add grid lines
    container
      .append("g")
      .attr("class", "grid")
      .selectAll("line")
      .data(yScale.ticks(5))
      .enter()
      .append("line")
      .attr("x1", 0)
      .attr("x2", innerWidth)
      .attr("y1", (d) => yScale(d))
      .attr("y2", (d) => yScale(d))
      .attr("stroke", "#2d3748")
      .attr("stroke-width", 1)

    // Add bars
    container
      .selectAll(".bar")
      .data(data.feeDistribution)
      .enter()
      .append("rect")
      .attr("class", "bar")
      .attr("x", (d) => xScale(d.category) as number)
      .attr("y", innerHeight)
      .attr("width", xScale.bandwidth())
      .attr("height", 0)
      .attr("fill", "#f6ad55")
      .transition()
      .duration(1000)
      .attr("y", (d) => yScale(d.count))
      .attr("height", (d) => innerHeight - yScale(d.count))
  }, [data, isLoading])

  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-[300px]">
        <Loader2 className="h-8 w-8 animate-spin text-gray-400" />
      </div>
    )
  }

  if (!data) {
    return (
      <div className="flex flex-col items-center justify-center h-[300px] text-gray-400">
        <p>No data available</p>
      </div>
    )
  }

  return (
    <Tabs defaultValue="transaction-rate" className="w-full">
      <TabsList className="grid grid-cols-3 mb-4">
        <TabsTrigger value="transaction-rate">Transaction Rate</TabsTrigger>
        <TabsTrigger value="confirmation-time">Confirmation Time</TabsTrigger>
        <TabsTrigger value="fee-distribution">Fee Distribution</TabsTrigger>
      </TabsList>

      <TabsContent value="transaction-rate" className="mt-0">
        <div className="space-y-4">
          <div className="flex justify-between items-center">
            <div>
              <h3 className="text-lg font-medium text-white">Transaction Rate</h3>
              <p className="text-sm text-gray-400">Transactions per minute over time</p>
            </div>
            <div className="text-right">
              <p className="text-2xl font-bold text-white">{data.currentTransactionRate.toFixed(2)}</p>
              <p className="text-sm text-gray-400">tx/min</p>
            </div>
          </div>
          <div className="w-full overflow-x-auto">
            <svg ref={transactionRateChartRef} className="min-w-[800px]" />
          </div>
        </div>
      </TabsContent>

      <TabsContent value="confirmation-time" className="mt-0">
        <div className="space-y-4">
          <div className="flex justify-between items-center">
            <div>
              <h3 className="text-lg font-medium text-white">Confirmation Time</h3>
              <p className="text-sm text-gray-400">Average time to confirmation in minutes</p>
            </div>
            <div className="text-right">
              <p className="text-2xl font-bold text-white">{data.currentConfirmationTime.toFixed(2)}</p>
              <p className="text-sm text-gray-400">minutes</p>
            </div>
          </div>
          <div className="w-full overflow-x-auto">
            <svg ref={confirmationTimeChartRef} className="min-w-[800px]" />
          </div>
        </div>
      </TabsContent>

      <TabsContent value="fee-distribution" className="mt-0">
        <div className="space-y-4">
          <div className="flex justify-between items-center">
            <div>
              <h3 className="text-lg font-medium text-white">Fee Distribution</h3>
              <p className="text-sm text-gray-400">Distribution of transaction fees</p>
            </div>
            <div className="text-right">
              <p className="text-2xl font-bold text-white">{data.averageFee.toFixed(8)}</p>
              <p className="text-sm text-gray-400">BTC avg fee</p>
            </div>
          </div>
          <div className="w-full overflow-x-auto">
            <svg ref={feeDistributionChartRef} className="min-w-[800px]" />
          </div>
        </div>
      </TabsContent>
    </Tabs>
  )
}

