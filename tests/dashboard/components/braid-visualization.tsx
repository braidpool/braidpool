"use client"

import { useEffect, useRef, useState } from "react"
import * as d3 from "d3"
import { Loader2, ZoomIn, ZoomOut, RotateCcw } from "lucide-react"
import type { BraidData } from "@/lib/types"
import { Button } from "@/components/ui/button"
import { Badge } from "@/components/ui/badge"

interface BraidVisualizationProps {
  data: BraidData | null
  isLoading: boolean
  filterOptions: {
    showPoolMinedOnly: boolean
    maxCohorts: number
    highlightHighestWorkPath: boolean
  }
}

export default function BraidVisualization({ data, isLoading, filterOptions }: BraidVisualizationProps) {
  const svgRef = useRef<SVGSVGElement>(null)
  const containerRef = useRef<HTMLDivElement>(null)
  const [dimensions, setDimensions] = useState({ width: 0, height: 0 })
  const [selectedBead, setSelectedBead] = useState<string | null>(null)
  const [zoomLevel, setZoomLevel] = useState(1)
  const zoomRef = useRef<d3.ZoomBehavior<Element, unknown> | null>(null)

  // Handle window resize
  useEffect(() => {
    const handleResize = () => {
      if (containerRef.current) {
        setDimensions({
          width: containerRef.current.clientWidth,
          height: 800, // Increased height for better visualization
        })
      }
    }

    handleResize() // Initial size

    window.addEventListener("resize", handleResize)
    return () => window.removeEventListener("resize", handleResize)
  }, [])

  // Render the visualization
  useEffect(() => {
    if (!svgRef.current || !data || !dimensions.width) return

    const svg = d3.select(svgRef.current)
    svg.selectAll("*").remove() // Clear previous rendering

    // Apply filters to the data
    let filteredBeads = [...data.beads]

    // Filter by pool mined if needed
    if (filterOptions.showPoolMinedOnly) {
      filteredBeads = filteredBeads.filter((bead) => bead.isPoolMined)
    }

    // Filter by max cohorts
    const maxCohort = Math.min(filterOptions.maxCohorts, Math.max(...filteredBeads.map((bead) => bead.cohort)))
    filteredBeads = filteredBeads.filter((bead) => bead.cohort <= maxCohort)

    // Group beads by cohort
    const cohorts = filteredBeads.reduce(
      (acc, bead) => {
        if (!acc[bead.cohort]) acc[bead.cohort] = []
        acc[bead.cohort].push(bead)
        return acc
      },
      {} as Record<number, typeof filteredBeads>,
    )

    const cohortKeys = Object.keys(cohorts)
      .map(Number)
      .sort((a, b) => a - b)

    // Calculate positions with optimized layout
    const beadRadius = 16 // Increased radius
    const blockSize = 32 // Increased block size
    const cohortSpacing = 180 // Increased horizontal spacing between cohorts
    const beadSpacing = 70 // Increased vertical spacing between beads

    // First pass: assign x positions based on cohort
    cohortKeys.forEach((cohortNum) => {
      const cohortBeads = cohorts[cohortNum]
      cohortBeads.forEach((bead) => {
        bead.x = 120 + cohortNum * cohortSpacing
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
                  const parent = filteredBeads.find((b) => b.id === pId)
                  return parent?.y || 0
                }),
              )
            : 0

        const bParentY =
          b.parents.length > 0
            ? Math.min(
                ...b.parents.map((pId) => {
                  const parent = filteredBeads.find((b) => b.id === pId)
                  return parent?.y || 0
                }),
              )
            : 0

        return aParentY - bParentY
      })

      // Assign y positions with improved spacing for flexibility
      cohortBeads.forEach((bead, i) => {
        // Center the highest work path
        if (bead.isHighestWorkPath) {
          bead.y = dimensions.height / 2
        } else {
          // Position other beads above or below the highest work path
          // Use a more spread out distribution to avoid overlaps
          const offset = i % 2 === 0 ? -beadSpacing * (Math.ceil(i / 2) + 0.5) : beadSpacing * (Math.ceil(i / 2) + 0.5)

          bead.y = dimensions.height / 2 + offset
        }
      })
    })

    // Add a dark background
    svg
      .append("rect")
      .attr("width", dimensions.width)
      .attr("height", dimensions.height)
      .attr("fill", "#111827") // Darker background
      .attr("rx", 8) // Rounded corners

    // Create a container for the graph with zoom capability
    const container = svg.attr("width", dimensions.width).attr("height", dimensions.height).append("g")

    // Add gradient definitions
    const defs = svg.append("defs")

    // Gradient for highest work path
    const hwpGradient = defs
      .append("linearGradient")
      .attr("id", "hwpGradient")
      .attr("x1", "0%")
      .attr("y1", "0%")
      .attr("x2", "100%")
      .attr("y2", "0%")

    hwpGradient.append("stop").attr("offset", "0%").attr("stop-color", "#ff4d6d")

    hwpGradient.append("stop").attr("offset", "100%").attr("stop-color", "#ff8fa3")

    // Gradient for pool-mined blocks
    const poolMinedGradient = defs
      .append("linearGradient")
      .attr("id", "poolMinedGradient")
      .attr("x1", "0%")
      .attr("y1", "0%")
      .attr("x2", "100%")
      .attr("y2", "100%")

    poolMinedGradient.append("stop").attr("offset", "0%").attr("stop-color", "#10b981")

    poolMinedGradient.append("stop").attr("offset", "100%").attr("stop-color", "#34d399")

    // Gradient for non-pool-mined blocks
    const nonPoolMinedGradient = defs
      .append("linearGradient")
      .attr("id", "nonPoolMinedGradient")
      .attr("x1", "0%")
      .attr("y1", "0%")
      .attr("x2", "100%")
      .attr("y2", "100%")

    nonPoolMinedGradient.append("stop").attr("offset", "0%").attr("stop-color", "#f59e0b")

    nonPoolMinedGradient.append("stop").attr("offset", "100%").attr("stop-color", "#fbbf24")

    // Gradient for regular beads
    const regularBeadGradient = defs
      .append("linearGradient")
      .attr("id", "regularBeadGradient")
      .attr("x1", "0%")
      .attr("y1", "0%")
      .attr("x2", "100%")
      .attr("y2", "100%")

    regularBeadGradient.append("stop").attr("offset", "0%").attr("stop-color", "#3b82f6")

    regularBeadGradient.append("stop").attr("offset", "100%").attr("stop-color", "#60a5fa")

    // Glow filter for hover effect
    const glowFilter = defs
      .append("filter")
      .attr("id", "glow")
      .attr("x", "-50%")
      .attr("y", "-50%")
      .attr("width", "200%")
      .attr("height", "200%")

    glowFilter.append("feGaussianBlur").attr("stdDeviation", "3").attr("result", "coloredBlur")

    const glowMerge = glowFilter.append("feMerge")
    glowMerge.append("feMergeNode").attr("in", "coloredBlur")
    glowMerge.append("feMergeNode").attr("in", "SourceGraphic")

    // Selected node glow filter
    const selectedGlowFilter = defs
      .append("filter")
      .attr("id", "selectedGlow")
      .attr("x", "-50%")
      .attr("y", "-50%")
      .attr("width", "200%")
      .attr("height", "200%")

    selectedGlowFilter.append("feGaussianBlur").attr("stdDeviation", "5").attr("result", "coloredBlur")

    const selectedGlowMerge = selectedGlowFilter.append("feMerge")
    selectedGlowMerge.append("feMergeNode").attr("in", "coloredBlur")
    selectedGlowMerge.append("feMergeNode").attr("in", "SourceGraphic")

    // Setup zoom behavior
    const zoom = d3
      .zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.3, 3])
      .on("zoom", (event) => {
        container.attr("transform", event.transform.toString())
        setZoomLevel(event.transform.k)
      })

    zoomRef.current = zoom
    svg.call(zoom)

    // Draw edges first (so they're behind the nodes)
    filteredBeads.forEach((bead) => {
      bead.parents.forEach((parentId) => {
        const parent = filteredBeads.find((b) => b.id === parentId)
        if (
          parent &&
          bead.x !== undefined &&
          bead.y !== undefined &&
          parent.x !== undefined &&
          parent.y !== undefined
        ) {
          // Calculate path with a smooth curve for better visualization
          const path = d3.line().curve(d3.curveBasis)([
            [parent.x, parent.y],
            [parent.x + (bead.x - parent.x) * 0.4, parent.y],
            [parent.x + (bead.x - parent.x) * 0.6, bead.y],
            [bead.x, bead.y],
          ])

          // Determine if this edge is part of the highest work path
          const isHighestWorkPath =
            filterOptions.highlightHighestWorkPath && bead.isHighestWorkPath && parent.isHighestWorkPath

          // Draw the edge
          const edge = container
            .append("path")
            .attr("d", path)
            .attr("stroke", isHighestWorkPath ? "url(#hwpGradient)" : "#4b5563")
            .attr("stroke-width", isHighestWorkPath ? 3 : 1.5)
            .attr("fill", "none")
            .attr("opacity", 0)
            .attr("class", "edge")
            .attr("data-source", parent.id)
            .attr("data-target", bead.id)

          // Add animation
          edge.transition().duration(1000).attr("opacity", 0.7).attr("stroke-dashoffset", 0)
        }
      })
    })

    // Draw nodes
    filteredBeads.forEach((bead) => {
      if (bead.x === undefined || bead.y === undefined) return

      const nodeGroup = container
        .append("g")
        .attr("transform", `translate(${bead.previousX || bead.x},${bead.previousY || bead.y})`)
        .attr("opacity", bead.previousX ? 0 : 1) // New nodes start invisible
        .attr("cursor", "pointer")
        .attr("class", "node")
        .attr("data-id", bead.id)
        .on("click", (event) => {
          event.stopPropagation() // Prevent triggering container click
          setSelectedBead(bead.id === selectedBead ? null : bead.id)

          // Highlight connected edges
          d3.selectAll(".edge").transition().duration(300).attr("opacity", 0.2)

          d3.selectAll(`.edge[data-source="${bead.id}"], .edge[data-target="${bead.id}"]`)
            .transition()
            .duration(300)
            .attr("opacity", 1)
            .attr("stroke-width", (d, i, nodes) => {
              const path = d3.select(nodes[i])
              return path.attr("stroke-width") === "3" ? 4 : 2.5
            })

          if (bead.id === selectedBead) {
            // If deselecting, reset all edges
            d3.selectAll(".edge")
              .transition()
              .duration(300)
              .attr("opacity", 0.7)
              .attr("stroke-width", (d, i, nodes) => {
                const path = d3.select(nodes[i])
                return path.attr("stroke") === "url(#hwpGradient)" ? 3 : 1.5
              })
          }
        })
        .on("mouseover", function () {
          // Apply glow effect on hover
          d3.select(this).select(".node-shape").attr("filter", "url(#glow)")

          // Show tooltip with basic info
          const tooltip = container
            .append("g")
            .attr("class", "tooltip")
            .attr("transform", `translate(${bead.x + 20},${bead.y - 30})`)

          tooltip
            .append("rect")
            .attr("rx", 5)
            .attr("ry", 5)
            .attr("width", 120)
            .attr("height", 50)
            .attr("fill", "#1f2937")
            .attr("stroke", "#374151")
            .attr("opacity", 0)
            .transition()
            .duration(200)
            .attr("opacity", 0.9)

          tooltip
            .append("text")
            .attr("x", 10)
            .attr("y", 20)
            .attr("fill", "white")
            .attr("font-size", "12px")
            .text(`ID: ${bead.id.substring(0, 8)}...`)

          tooltip
            .append("text")
            .attr("x", 10)
            .attr("y", 40)
            .attr("fill", "white")
            .attr("font-size", "12px")
            .text(`Type: ${bead.isBlock ? "Block" : "Transaction"}`)
        })
        .on("mouseout", function () {
          // Remove glow effect unless selected
          if (bead.id !== selectedBead) {
            d3.select(this).select(".node-shape").attr("filter", null)
          }

          // Remove tooltip
          container.selectAll(".tooltip").remove()
        })

      // Animate to new position if there was a previous position
      if (bead.previousX !== undefined && bead.previousY !== undefined) {
        nodeGroup.transition().duration(1000).attr("transform", `translate(${bead.x},${bead.y})`).attr("opacity", 1)
      } else {
        // Entrance animation for new nodes
        nodeGroup
          .attr("transform", `translate(${bead.x},${bead.y - 50})`)
          .attr("opacity", 0)
          .transition()
          .duration(800)
          .attr("transform", `translate(${bead.x},${bead.y})`)
          .attr("opacity", 1)
          .ease(d3.easeBounce)
      }

      // Determine node color based on type and status
      let fillColor = "url(#regularBeadGradient)" // Default gradient

      if (bead.isHighestWorkPath && filterOptions.highlightHighestWorkPath) {
        fillColor = "url(#hwpGradient)" // Red gradient for highest work path
      } else if (bead.isBlock) {
        fillColor = bead.isPoolMined ? "url(#poolMinedGradient)" : "url(#nonPoolMinedGradient)"
      }

      // Add pulse animation for selected bead
      if (selectedBead === bead.id) {
        // Pulsing circle behind the node
        nodeGroup
          .append("circle")
          .attr("r", bead.isBlock ? blockSize * 0.9 : beadRadius * 1.8)
          .attr("fill", "none")
          .attr("stroke", "#60a5fa")
          .attr("stroke-width", 2)
          .attr("opacity", 0.7)
          .attr("filter", "url(#selectedGlow)")
          .attr("class", "pulse-circle")
      }

      // Node shape (circle or square)
      const nodeShape = bead.isBlock
        ? nodeGroup
            .append("rect")
            .attr("width", blockSize)
            .attr("height", blockSize)
            .attr("x", -blockSize / 2)
            .attr("y", -blockSize / 2)
            .attr("rx", 6)
            .attr("class", "node-shape")
        : nodeGroup.append("circle").attr("r", beadRadius).attr("class", "node-shape")

      // Apply fill and style
      nodeShape
        .attr("fill", fillColor)
        .attr("stroke", "#1a202c")
        .attr("stroke-width", 2)
        .attr("filter", selectedBead === bead.id ? "url(#selectedGlow)" : null)

      // Add subtle animation for all nodes
      nodeShape.attr("transform", "scale(0.9)").transition().duration(500).attr("transform", "scale(1)")

      // Add label
      nodeGroup
        .append("text")
        .attr("text-anchor", "middle")
        .attr("dy", bead.isBlock ? "0.3em" : "0.3em")
        .attr("fill", "white")
        .attr("font-size", "10px")
        .attr("font-weight", "bold")
        .attr("pointer-events", "none") // Prevent text from interfering with click events
        .text(bead.id.substring(0, 6)) // Show shortened ID

      // Add small badge for pool-mined status on blocks
      if (bead.isBlock) {
        const badgeColor = bead.isPoolMined ? "#10b981" : "#f59e0b"
        const badgeText = bead.isPoolMined ? "P" : "NP"

        nodeGroup
          .append("circle")
          .attr("cx", blockSize / 2 - 2)
          .attr("cy", -blockSize / 2 + 2)
          .attr("r", 8)
          .attr("fill", badgeColor)
          .attr("stroke", "#1a202c")
          .attr("stroke-width", 1)

        nodeGroup
          .append("text")
          .attr("x", blockSize / 2 - 2)
          .attr("y", -blockSize / 2 + 2)
          .attr("text-anchor", "middle")
          .attr("dy", "0.3em")
          .attr("fill", "white")
          .attr("font-size", "8px")
          .attr("font-weight", "bold")
          .attr("pointer-events", "none")
          .text(badgeText)
      }
    })

    // Add legend
    const legend = svg
      .append("g")
      .attr("transform", `translate(${dimensions.width - 200}, 20)`)
      .attr("class", "legend")

    // Highest work path
    if (filterOptions.highlightHighestWorkPath) {
      legend
        .append("line")
        .attr("x1", 0)
        .attr("y1", 0)
        .attr("x2", 30)
        .attr("y2", 0)
        .attr("stroke", "url(#hwpGradient)")
        .attr("stroke-width", 3)

      legend
        .append("text")
        .attr("x", 40)
        .attr("y", 4)
        .attr("fill", "#e2e8f0")
        .text("Highest Work Path")
        .attr("font-size", "12px")
    }

    // Pool-mined block
    legend
      .append("rect")
      .attr("x", 0)
      .attr("y", 20)
      .attr("width", 20)
      .attr("height", 20)
      .attr("rx", 3)
      .attr("fill", "url(#poolMinedGradient)")
      .attr("stroke", "#1a202c")

    legend
      .append("text")
      .attr("x", 40)
      .attr("y", 32)
      .attr("fill", "#e2e8f0")
      .text("Pool-mined Block")
      .attr("font-size", "12px")

    // Non-pool-mined block
    legend
      .append("rect")
      .attr("x", 0)
      .attr("y", 50)
      .attr("width", 20)
      .attr("height", 20)
      .attr("rx", 3)
      .attr("fill", "url(#nonPoolMinedGradient)")
      .attr("stroke", "#1a202c")

    legend
      .append("text")
      .attr("x", 40)
      .attr("y", 62)
      .attr("fill", "#e2e8f0")
      .text("Non-pool Block")
      .attr("font-size", "12px")

    // Regular bead
    legend
      .append("circle")
      .attr("cx", 10)
      .attr("cy", 90)
      .attr("r", 10)
      .attr("fill", "url(#regularBeadGradient)")
      .attr("stroke", "#1a202c")

    legend
      .append("text")
      .attr("x", 40)
      .attr("y", 94)
      .attr("fill", "#e2e8f0")
      .text("Transaction")
      .attr("font-size", "12px")

    // Add click handler to clear selection when clicking on empty space
    svg.on("click", () => {
      if (selectedBead) {
        setSelectedBead(null)

        // Reset all edges
        d3.selectAll(".edge")
          .transition()
          .duration(300)
          .attr("opacity", 0.7)
          .attr("stroke-width", (d, i, nodes) => {
            const path = d3.select(nodes[i])
            return path.attr("stroke") === "url(#hwpGradient)" ? 3 : 1.5
          })
      }
    })

    // Add pulse animation for selected nodes
    if (selectedBead) {
      const pulseAnimation = () => {
        d3.selectAll(".pulse-circle")
          .transition()
          .duration(1500)
          .attr("r", function () {
            const currentR = Number.parseFloat(d3.select(this).attr("r"))
            return currentR * 1.3
          })
          .attr("opacity", 0.2)
          .on("end", function () {
            d3.select(this)
              .attr("r", function () {
                // Reset to original size
                const parent = d3.select(this.parentNode)
                const isBlock = parent.select("rect").size() > 0
                return isBlock ? blockSize * 0.9 : beadRadius * 1.8
              })
              .attr("opacity", 0.7)
              .call(() => pulseAnimation())
          })
      }

      pulseAnimation()
    }
  }, [data, dimensions, filterOptions, selectedBead])

  // Handle zoom controls
  const handleZoomIn = () => {
    if (svgRef.current && zoomRef.current) {
      d3.select(svgRef.current).transition().call(zoomRef.current.scaleBy, 1.3)
    }
  }

  const handleZoomOut = () => {
    if (svgRef.current && zoomRef.current) {
      d3.select(svgRef.current).transition().call(zoomRef.current.scaleBy, 0.7)
    }
  }

  const handleResetZoom = () => {
    if (svgRef.current && zoomRef.current) {
      d3.select(svgRef.current).transition().call(zoomRef.current.transform, d3.zoomIdentity)
    }
  }

  // Show loading state
  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-[800px] bg-gray-900 rounded-lg">
        <div className="flex flex-col items-center gap-4">
          <Loader2 className="h-12 w-12 animate-spin text-blue-400" />
          <p className="text-gray-400">Loading visualization data...</p>
        </div>
      </div>
    )
  }

  // Show empty state
  if (!data || data.beads.length === 0) {
    return (
      <div className="flex flex-col items-center justify-center h-[800px] bg-gray-900 rounded-lg text-gray-400">
        <p className="text-xl">No data available</p>
        <p className="text-sm mt-2">Try adjusting your filters or refreshing the dashboard</p>
      </div>
    )
  }

  // Show selected bead details
  const selectedBeadData = data.beads.find((bead) => bead.id === selectedBead)

  return (
    <div className="relative">
      {/* Zoom controls */}
      <div className="absolute top-4 left-4 z-10 flex flex-col gap-2">
        <Button variant="secondary" size="icon" onClick={handleZoomIn} className="bg-gray-800 hover:bg-gray-700">
          <ZoomIn className="h-4 w-4" />
        </Button>
        <Button variant="secondary" size="icon" onClick={handleZoomOut} className="bg-gray-800 hover:bg-gray-700">
          <ZoomOut className="h-4 w-4" />
        </Button>
        <Button variant="secondary" size="icon" onClick={handleResetZoom} className="bg-gray-800 hover:bg-gray-700">
          <RotateCcw className="h-4 w-4" />
        </Button>
      </div>

      {/* Zoom level indicator */}
      <div className="absolute top-4 right-4 z-10">
        <Badge variant="outline" className="bg-gray-800 text-gray-300">
          Zoom: {Math.round(zoomLevel * 100)}%
        </Badge>
      </div>

      <div ref={containerRef} className="w-full">
        <svg ref={svgRef} className="w-full" style={{ height: "800px" }}></svg>
      </div>

      {selectedBead && selectedBeadData && (
        <div className="absolute top-16 right-4 bg-gray-800 border border-gray-700 rounded-lg p-4 shadow-lg max-w-xs z-20">
          <div className="flex justify-between items-start">
            <h3 className="text-sm font-medium text-white mb-2">
              {selectedBeadData.isBlock ? "Block Details" : "Transaction Details"}
            </h3>
            <Button
              variant="ghost"
              size="sm"
              className="h-6 w-6 p-0 text-gray-400 hover:text-white"
              onClick={() => setSelectedBead(null)}
            >
              ×
            </Button>
          </div>
          <div className="space-y-2 text-xs">
            <div className="flex justify-between">
              <span className="text-gray-400">ID:</span>
              <span className="text-white font-mono">{selectedBeadData.id.substring(0, 10)}...</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Type:</span>
              <span className="text-white">{selectedBeadData.isBlock ? "Block" : "Transaction"}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Cohort:</span>
              <span className="text-white">{selectedBeadData.cohort}</span>
            </div>
            {selectedBeadData.isBlock && (
              <div className="flex justify-between">
                <span className="text-gray-400">Pool Mined:</span>
                <span className="text-white">{selectedBeadData.isPoolMined ? "Yes" : "No"}</span>
              </div>
            )}
            <div className="flex justify-between">
              <span className="text-gray-400">Highest Work Path:</span>
              <span className="text-white">{selectedBeadData.isHighestWorkPath ? "Yes" : "No"}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Parents:</span>
              <span className="text-white">{selectedBeadData.parents.length}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-400">Children:</span>
              <span className="text-white">{selectedBeadData.children.length}</span>
            </div>

            {/* Connection details */}
            <div className="mt-4 pt-2 border-t border-gray-700">
              <h4 className="text-xs font-medium text-gray-300 mb-2">Connections</h4>
              <div className="space-y-1">
                <div className="flex items-center gap-2">
                  <div className="w-3 h-3 rounded-full bg-blue-500"></div>
                  <span className="text-gray-400">
                    Parents: {selectedBeadData.parents.map((p) => p.substring(0, 6)).join(", ")}
                  </span>
                </div>
                <div className="flex items-center gap-2">
                  <div className="w-3 h-3 rounded-full bg-green-500"></div>
                  <span className="text-gray-400">
                    Children: {selectedBeadData.children.map((c) => c.substring(0, 6)).join(", ")}
                  </span>
                </div>
              </div>
            </div>
          </div>
        </div>
      )}

      {/* Instructions overlay */}
      <div className="absolute bottom-4 left-4 bg-gray-800/80 backdrop-blur-sm border border-gray-700 rounded-lg p-3 text-xs text-gray-300 max-w-xs">
        <p className="font-medium mb-1">Interaction Tips:</p>
        <ul className="list-disc list-inside space-y-1 text-gray-400">
          <li>Click on a node to see details</li>
          <li>Use zoom controls to navigate</li>
          <li>Hover over nodes for quick info</li>
          <li>Click empty space to deselect</li>
        </ul>
      </div>
    </div>
  )
}

