"use client"

import { useEffect, useRef, useState } from "react"
import * as d3 from "d3"
import { ChevronRight, Info } from "lucide-react"
import { Button } from "@/components/ui/button"
import { Tooltip, TooltipContent, TooltipProvider, TooltipTrigger } from "@/components/ui/tooltip"

// Types for our DAG structure
interface Bead {
  id: string
  cohort: number
  isBlock: boolean
  isHighestWorkPath: boolean
  parents: string[]
  children: string[]
  x?: number
  y?: number
  previousX?: number
  previousY?: number
}

interface BraidData {
  beads: Bead[]
}

export default function BraidVisualization() {
  const svgRef = useRef<SVGSVGElement>(null)
  const [showControls, setShowControls] = useState(false)

  // Sample data - you would replace this with your actual data
  const [data, setData] = useState<BraidData>({
    beads: [
      {
        id: "block1",
        cohort: 0,
        isBlock: true,
        isHighestWorkPath: true,
        parents: [],
        children: ["bead2", "bead3", "block2"],
      },
      { id: "bead2", cohort: 1, isBlock: false, isHighestWorkPath: false, parents: ["block1"], children: ["bead4"] },
      { id: "bead3", cohort: 1, isBlock: false, isHighestWorkPath: false, parents: ["block1"], children: ["bead5"] },
      {
        id: "block2",
        cohort: 1,
        isBlock: true,
        isHighestWorkPath: true,
        parents: ["block1"],
        children: ["bead4", "bead5", "block3"],
      },
      {
        id: "bead4",
        cohort: 2,
        isBlock: false,
        isHighestWorkPath: false,
        parents: ["bead2", "block2"],
        children: ["bead6"],
      },
      {
        id: "bead5",
        cohort: 2,
        isBlock: false,
        isHighestWorkPath: false,
        parents: ["bead3", "block2"],
        children: ["bead7"],
      },
      {
        id: "block3",
        cohort: 2,
        isBlock: true,
        isHighestWorkPath: true,
        parents: ["block2"],
        children: ["bead6", "bead7", "block4"],
      },
      { id: "bead6", cohort: 3, isBlock: false, isHighestWorkPath: false, parents: ["bead4", "block3"], children: [] },
      { id: "bead7", cohort: 3, isBlock: false, isHighestWorkPath: false, parents: ["bead5", "block3"], children: [] },
      { id: "block4", cohort: 3, isBlock: true, isHighestWorkPath: true, parents: ["block3"], children: [] },
    ],
  })

  // Add a new bead to demonstrate animation
  const addNewBead = () => {
    const newBead: Bead = {
      id: `bead${data.beads.length + 1}`,
      cohort: 3,
      isBlock: false,
      isHighestWorkPath: false,
      parents: ["bead6"],
      children: [],
    }

    // Update parent's children
    const updatedBeads = data.beads.map((bead) => {
      if (bead.id === "bead6") {
        return {
          ...bead,
          children: [...bead.children, newBead.id],
        }
      }
      return bead
    })

    // Store current positions for animation
    const beadsWithPreviousPositions = updatedBeads.map((bead) => ({
      ...bead,
      previousX: bead.x,
      previousY: bead.y,
    }))

    setData({
      beads: [...beadsWithPreviousPositions, newBead],
    })
  }

  // Optimize bead placement and render the graph
  useEffect(() => {
    if (!svgRef.current) return

    const svg = d3.select(svgRef.current)
    svg.selectAll("*").remove()

    const width = 800
    const height = 600
    const margin = { top: 40, right: 40, bottom: 40, left: 40 }

    // Group beads by cohort
    const cohorts = data.beads.reduce(
      (acc, bead) => {
        if (!acc[bead.cohort]) acc[bead.cohort] = []
        acc[bead.cohort].push(bead)
        return acc
      },
      {} as Record<number, Bead[]>,
    )

    const cohortKeys = Object.keys(cohorts)
      .map(Number)
      .sort((a, b) => a - b)

    // Calculate positions with optimized layout
    const beadRadius = 15
    const blockSize = 30
    const cohortSpacing = 150 // Horizontal spacing between cohorts
    const beadSpacing = 60 // Vertical spacing between beads

    // First pass: assign x positions based on cohort
    cohortKeys.forEach((cohortNum) => {
      const cohortBeads = cohorts[cohortNum]
      cohortBeads.forEach((bead) => {
        bead.x = margin.left + cohortNum * cohortSpacing
      })
    })

    // Second pass: optimize y positions to minimize crossings
    cohortKeys.forEach((cohortNum) => {
      const cohortBeads = cohorts[cohortNum]

      // Sort beads: highest work path first, then by parent positions
      cohortBeads.sort((a, b) => {
        // Highest work path beads come first
        if (a.isHighestWorkPath && !b.isHighestWorkPath) return -1
        if (!a.isHighestWorkPath && b.isHighestWorkPath) return 1

        // If both are on highest work path or both are not, sort by parent positions
        const aParentY =
          a.parents.length > 0
            ? Math.min(
                ...a.parents.map((pId) => {
                  const parent = data.beads.find((b) => b.id === pId)
                  return parent?.y || 0
                }),
              )
            : 0

        const bParentY =
          b.parents.length > 0
            ? Math.min(
                ...b.parents.map((pId) => {
                  const parent = data.beads.find((b) => b.id === pId)
                  return parent?.y || 0
                }),
              )
            : 0

        return aParentY - bParentY
      })

      // Assign y positions with half-positions for flexibility
      cohortBeads.forEach((bead, i) => {
        // Center the highest work path
        if (bead.isHighestWorkPath) {
          bead.y = height / 2
        } else {
          // Position other beads above or below the highest work path
          const offset = i % 2 === 0 ? -beadSpacing * Math.ceil(i / 2) : beadSpacing * Math.ceil(i / 2)

          bead.y = height / 2 + offset
        }
      })
    })

    // Create a container for the graph with zoom capability
    const container = svg
      .attr("width", width + margin.left + margin.right)
      .attr("height", height + margin.top + margin.bottom)
      .call(
        d3.zoom<SVGSVGElement, unknown>().on("zoom", (event) => {
          container.attr("transform", event.transform.toString())
        }) as any,
      )
      .append("g")
      .attr("transform", `translate(${margin.left},${margin.top})`)

    // Draw edges first (so they're behind the nodes)
    data.beads.forEach((bead) => {
      bead.parents.forEach((parentId) => {
        const parent = data.beads.find((b) => b.id === parentId)
        if (
          parent &&
          bead.x !== undefined &&
          bead.y !== undefined &&
          parent.x !== undefined &&
          parent.y !== undefined
        ) {
          // Calculate path
          const path = d3.line()([
            [parent.x, parent.y],
            [bead.x, bead.y],
          ])

          // Draw the edge
          container
            .append("path")
            .attr("d", path)
            .attr("stroke", bead.isHighestWorkPath && parent.isHighestWorkPath ? "#ff6b6b" : "#aaa")
            .attr("stroke-width", bead.isHighestWorkPath && parent.isHighestWorkPath ? 3 : 1.5)
            .attr("fill", "none")
            .attr("opacity", 0)
            .transition()
            .duration(800)
            .attr("opacity", 1)
        }
      })
    })

    // Draw nodes
    data.beads.forEach((bead) => {
      if (bead.x === undefined || bead.y === undefined) return

      const nodeGroup = container
        .append("g")
        .attr("transform", `translate(${bead.previousX || bead.x},${bead.previousY || bead.y})`)
        .attr("opacity", bead.previousX ? 0 : 1) // New nodes start invisible

      // Animate to new position if there was a previous position
      if (bead.previousX !== undefined && bead.previousY !== undefined) {
        nodeGroup.transition().duration(800).attr("transform", `translate(${bead.x},${bead.y})`).attr("opacity", 1)
      }

      if (bead.isBlock) {
        // Draw blocks as squares
        nodeGroup
          .append("rect")
          .attr("width", blockSize)
          .attr("height", blockSize)
          .attr("x", -blockSize / 2)
          .attr("y", -blockSize / 2)
          .attr("rx", 3)
          .attr("fill", bead.isHighestWorkPath ? "#ff6b6b" : "#6b9fff")
          .attr("stroke", "#333")
          .attr("stroke-width", 2)
      } else {
        // Draw regular beads as circles
        nodeGroup
          .append("circle")
          .attr("r", beadRadius)
          .attr("fill", bead.isHighestWorkPath ? "#ff6b6b" : "#6b9fff")
          .attr("stroke", "#333")
          .attr("stroke-width", 2)
      }

      // Add label
      nodeGroup
        .append("text")
        .attr("text-anchor", "middle")
        .attr("dy", bead.isBlock ? "0.3em" : "0.3em")
        .attr("fill", "white")
        .attr("font-size", "10px")
        .attr("font-weight", "bold")
        .text(bead.id)
    })

    // Add legend
    const legend = svg.append("g").attr("transform", `translate(${width - 150}, 20)`)

    // Highest work path
    legend
      .append("line")
      .attr("x1", 0)
      .attr("y1", 0)
      .attr("x2", 20)
      .attr("y2", 0)
      .attr("stroke", "#ff6b6b")
      .attr("stroke-width", 3)

    legend.append("text").attr("x", 25).attr("y", 4).text("Highest Work Path").attr("font-size", "12px")

    // Block
    legend
      .append("rect")
      .attr("x", 0)
      .attr("y", 15)
      .attr("width", 15)
      .attr("height", 15)
      .attr("fill", "#6b9fff")
      .attr("stroke", "#333")

    legend.append("text").attr("x", 25).attr("y", 27).text("Block").attr("font-size", "12px")

    // Regular bead
    legend.append("circle").attr("cx", 7.5).attr("cy", 45).attr("r", 7.5).attr("fill", "#6b9fff").attr("stroke", "#333")

    legend.append("text").attr("x", 25).attr("y", 48).text("Regular Bead").attr("font-size", "12px")
  }, [data])

  return (
    <div className="flex flex-col items-center w-full max-w-4xl mx-auto p-4 space-y-4">
      <div className="w-full flex justify-between items-center">
        <h2 className="text-2xl font-bold">Braid (DAG) Visualization</h2>
        <div className="flex items-center space-x-2">
          <TooltipProvider>
            <Tooltip>
              <TooltipTrigger asChild>
                <Button variant="outline" size="icon">
                  <Info className="h-4 w-4" />
                </Button>
              </TooltipTrigger>
              <TooltipContent className="max-w-sm">
                <p>
                  This visualization shows a Directed Acyclic Graph (DAG) with optimized bead placement. The red path
                  represents the Highest Work Path. Squares are blocks, circles are regular beads.
                </p>
              </TooltipContent>
            </Tooltip>
          </TooltipProvider>
          <Button variant="outline" onClick={() => setShowControls(!showControls)} className="flex items-center">
            Controls
            <ChevronRight className={`ml-2 h-4 w-4 transition-transform ${showControls ? "rotate-90" : ""}`} />
          </Button>
        </div>
      </div>

      {showControls && (
        <div className="w-full p-4 border rounded-md bg-muted/50">
          <div className="flex flex-wrap gap-4">
            <Button onClick={addNewBead}>Add New Bead</Button>
          </div>
        </div>
      )}

      <div className="w-full border rounded-lg overflow-hidden bg-white">
        <svg ref={svgRef} className="w-full" style={{ minHeight: "600px" }}></svg>
      </div>
    </div>
  )
}

