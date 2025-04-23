"use client"
import { useEffect, useRef } from "react"
import { Layers } from "lucide-react"
import gsap from "gsap"
import ScrollTrigger from "gsap/ScrollTrigger"

gsap.registerPlugin(ScrollTrigger)

export function BlockTimeline({
  blockVisualizationData,
  isLoaded,
}: {
  blockVisualizationData: any[]
  isLoaded: boolean
}) {
  const containerRef = useRef<HTMLDivElement>(null)
  const lineRef = useRef<HTMLDivElement>(null)
  const dotsRef = useRef<(HTMLDivElement | null)[]>([])
  const blocksRef = useRef<(HTMLDivElement | null)[]>([])

  useEffect(() => {
    if (!containerRef.current) return

    // Kill any existing ScrollTriggers to avoid duplicates
    ScrollTrigger.getAll().forEach(trigger => trigger.kill())

    // Animate the line growing from top to bottom
    gsap.fromTo(lineRef.current,
      { scaleY: 0, transformOrigin: "top center" },
      {
        scaleY: 1,
        duration: 1,
        ease: "none",
        scrollTrigger: {
          trigger: containerRef.current,
          start: "top center",
          end: "bottom center",
          scrub: true,
        }
      }
    )

    // Create separate animations for each dot and block
    dotsRef.current.forEach((dot, index) => {
      if (!dot || !blocksRef.current[index]) return

      // Calculate when this dot should appear (based on its position)
      const startPos = index * 0.1 + 0.2
      const endPos = startPos + 0.1

      // Dot appears when line reaches it
      gsap.fromTo(dot,
        { opacity: 0, scale: 0 },
        {
          opacity: 1,
          scale: 1,
          duration: 0.5,
          scrollTrigger: {
            trigger: containerRef.current,
            start: `${startPos * 100}% center`,
            end: `${endPos * 100}% center`,
            scrub: true,
            toggleActions: "play none none none"
          }
        }
      )

      // Block appears immediately after dot
      gsap.fromTo(blocksRef.current[index],
        { opacity: 0, x: index % 2 === 0 ? 50 : -50 },
        {
          opacity: 1,
          x: 0,
          duration: 0.8,
          scrollTrigger: {
            trigger: containerRef.current,
            start: `${(startPos + 0.05) * 100}% center`,
            end: `${(endPos + 0.2) * 100}% center`,
            scrub: true,
            toggleActions: "play none none none"
          }
        }
      )
    })

  }, [blockVisualizationData])

  if (!isLoaded)
    return (
      <div className="absolute inset-0 flex items-center justify-center">
        <div className="w-12 h-12 border-4 border-blue-500 border-t-transparent rounded-full animate-spin"></div>
      </div>
    )

  return (
    <div className="relative h-[200vh]" ref={containerRef}>
      {/* Timeline line - will grow as we scroll */}
      <div 
        ref={lineRef}
        className="absolute left-1/2 top-0 bottom-0 w-1 bg-blue-500 z-0"
        style={{ transform: "scaleY(0)", transformOrigin: "top center" }}
      />

      <div className="relative z-20" style={{ height: "200vh" }}>
        {blockVisualizationData.slice(0, 5).map((block, index) => {
          // Calculate vertical position for each block (spaced evenly)
          const topPosition = `${1 + index * 10}%`
          
          return (
            <div
              key={block.id}
              className="absolute left-0 right-0"
              style={{ top: topPosition }}
            >
              {/* Timeline dot - will appear when line reaches it */}
              <div
                ref={el => dotsRef.current[index] = el}
                className="absolute left-[51%] top-0 w-4 h-4 rounded-full bg-blue-500 -ml-2 z-20 opacity-0"
                style={{ transform: "translateX(-50%) scale(0)" }}
              />

              {/* Block content - will slide in after dot appears */}
              <div
                
                className={`w-5/12 ${
                  index % 2 === 0 ? "ml-auto pl-8" : "mr-auto pr-8"
                } opacity-0`}
                style={{
                  transform: index % 2 === 0 ? "translateX(50px)" : "translateX(-50px)"
                }}
              >
                <div className="border border-gray-200/20 rounded-lg p-4 bg-gray-900/50 backdrop-blur-sm">
                  <div className="flex justify-between items-start mb-2">
                    <h3 className="text-lg font-semibold text-white">
                      Block #{block.height}
                    </h3>
                    <div className="bg-blue-500/20 p-1.5 rounded-lg">
                      <Layers className="h-4 w-4 text-blue-400" />
                    </div>
                  </div>
                  <div className="text-sm text-gray-300 mb-2">
                    {new Date(block.timestamp).toLocaleString()}
                  </div>
                  <div className="grid grid-cols-2 gap-2 text-sm">
                    <div className="flex justify-between">
                      <span className="text-gray-400">Txs:</span>
                      <span className="text-blue-300">{block.transactions}</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-gray-400">Size:</span>
                      <span className="text-blue-300">{block.size} KB</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-gray-400">Miner:</span>
                      <span className="text-blue-300 truncate max-w-[120px]">
                        {block.miner}
                      </span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-gray-400">Diff:</span>
                      <span className="text-blue-300">{block.difficulty}</span>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}