import { motion, useAnimation, useInView } from "framer-motion"
import { useRef, useEffect, useState } from "react"

export default function MiningChart({ isLoaded }: { isLoaded: boolean }) {
  const [chartHovered, setChartHovered] = useState(false)
  const chartRef = useRef(null)
  const isChartInView = useInView(chartRef, { once: false, amount: 0.3 })
  const chartControls = useAnimation()

  useEffect(() => {
    if (isChartInView) {
      chartControls.start({
        pathLength: 1,
        transition: { duration: 2, ease: "easeInOut" },
      })
    } else {
      chartControls.start({
        pathLength: 0,
        transition: { duration: 0.5 },
      })
    }
  }, [isChartInView, chartControls])

  return (
    <motion.div
      ref={chartRef}
      initial={{ opacity: 0, y: 30, rotateX: 5 }}
      animate={{
        opacity: isLoaded ? 1 : 0,
        y: isLoaded ? 0 : 30,
        rotateX: 0,
        boxShadow: chartHovered ? "0 0 30px rgba(59,130,246,0.3)" : "0 0 20px rgba(59,130,246,0.15)",
      }}
      transition={{ duration: 0.7, delay: 0.6, type: "spring" }}
      className="border border-gray-800/50 rounded-xl p-4 h-64 relative bg-black/30 backdrop-blur-md overflow-hidden transform-gpu"
      onMouseEnter={() => setChartHovered(true)}
      onMouseLeave={() => setChartHovered(false)}
    >
      {/* Animated gradient background */}
      <motion.div
        className="absolute inset-0 bg-gradient-to-br from-blue-900/10 via-transparent to-purple-900/10"
        animate={{
          opacity: chartHovered ? 0.8 : 0.3,
          backgroundPosition: ["0% 0%", "100% 100%", "0% 0%"],
        }}
        transition={{
          opacity: { duration: 0.5 },
          backgroundPosition: {
            duration: 15,
            repeat: Number.POSITIVE_INFINITY,
            repeatType: "loop",
          },
        }}
      />

      {/* SVG Line Chart */}
      <svg className="w-full h-full" viewBox="0 0 800 200">
        <defs>
          <linearGradient id="lineGradient" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor="#3b82f6" />
            <stop offset="50%" stopColor="#8b5cf6" />
            <stop offset="100%" stopColor="#3b82f6" />
          </linearGradient>

          <linearGradient id="areaGradient" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor="#3b82f6" stopOpacity="0.3" />
            <stop offset="100%" stopColor="#3b82f6" stopOpacity="0" />
          </linearGradient>

          <filter id="glow" x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feComposite in="SourceGraphic" in2="blur" operator="over" />
          </filter>

          <filter id="softGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="10" result="blur" />
            <feComposite in="SourceGraphic" in2="blur" operator="over" />
          </filter>

          <linearGradient id="animatedGradient" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor="#3b82f6">
              <animate attributeName="stop-color" values="#3b82f6; #8b5cf6; #3b82f6" dur="4s" repeatCount="indefinite" />
            </stop>
            <stop offset="50%" stopColor="#8b5cf6">
              <animate attributeName="stop-color" values="#8b5cf6; #3b82f6; #8b5cf6" dur="4s" repeatCount="indefinite" />
            </stop>
            <stop offset="100%" stopColor="#3b82f6">
              <animate attributeName="stop-color" values="#3b82f6; #8b5cf6; #3b82f6" dur="4s" repeatCount="indefinite" />
            </stop>
          </linearGradient>
        </defs>

        {/* Background grid */}
        <g className="opacity-20">
          {[0, 50, 100, 150].map((y) => (
            <motion.line
              key={`grid-h-${y}`}
              x1="0"
              y1={y}
              x2="800"
              y2={y}
              stroke="#4b5563"
              strokeWidth="1"
              strokeDasharray="5,5"
              initial={{ opacity: 0 }}
              animate={{ opacity: 0.5 }}
              transition={{ duration: 1, delay: y * 0.01 }}
            />
          ))}
          {[0, 100, 200, 300, 400, 500, 600, 700, 800].map((x) => (
            <motion.line
              key={`grid-v-${x}`}
              x1={x}
              y1="0"
              x2={x}
              y2="200"
              stroke="#4b5563"
              strokeWidth="1"
              strokeDasharray="5,5"
              initial={{ opacity: 0 }}
              animate={{ opacity: 0.5 }}
              transition={{ duration: 1, delay: x * 0.001 }}
            />
          ))}
        </g>

        {/* Area under the curve */}
        <motion.path
          d="M0,100 C50,80 100,120 150,100 C200,80 250,120 300,80 C350,40 400,120 450,100 C500,80 550,40 600,80 C650,120 700,80 750,100 C800,120 L800,200 L0,200 Z"
          fill="url(#areaGradient)"
          initial={{ opacity: 0 }}
          animate={{ opacity: chartHovered ? 0.8 : 0.3 }}
          transition={{ duration: 0.5 }}
        />

        {/* Main line */}
        <motion.path
          d="M0,100 C50,80 100,120 150,100 C200,80 250,120 300,80 C350,40 400,120 450,100 C500,80 550,40 600,80 C650,120 700,80 750,100 C800,120"
          fill="none"
          stroke={chartHovered ? "url(#animatedGradient)" : "url(#lineGradient)"}
          strokeWidth={chartHovered ? "4" : "3"}
          filter="url(#glow)"
          initial={{ pathLength: 0 }}
          animate={chartControls}
        />


        {/* Data points */}
        {[
          { x: 150, y: 100, value: "128 BTC" },
          { x: 300, y: 80, value: "96 BTC" },
          { x: 450, y: 100, value: "128 BTC" },
          { x: 600, y: 80, value: "96 BTC" },
        ].map((point, i) => (
          <DataPoint 
            key={i}
            x={point.x}
            y={point.y}
            value={point.value}
            index={i}
            hovered={chartHovered}
          />
        ))}
      </svg>

      {/* X-axis labels */}
      <div className="absolute bottom-0 left-0 right-0 flex justify-between text-xs px-4">
        {["Aug 1", "Aug 5", "Aug 9", "Aug 13", "Aug 13", "Aug 17", "Aug 21", "Aug 25", "Aug 29"].map((label, i) => (
          <motion.div
            key={i}
            className="text-blue-300 hover:text-blue-200 cursor-pointer transition-colors duration-300"
            whileHover={{ y: -2, scale: 1.1 }}
            transition={{ type: "spring", stiffness: 300 }}
          >
            {label}
          </motion.div>
        ))}
      </div>
    </motion.div>
  )
}

function DataPoint({
  x,
  y,
  value,
  index,
  hovered
}: {
  x: number
  y: number
  value: string
  index: number
  hovered: boolean
}) {
  return (
    <motion.g>
      {/* Outer glow */}
      <motion.circle
        cx={x}
        cy={y}
        r={hovered ? 12 : 8}
        fill="rgba(59, 130, 246, 0.3)"
        filter="url(#softGlow)"
        animate={{
          r: hovered ? [8, 12, 8] : [6, 8, 6],
          opacity: hovered ? [0.5, 0.8, 0.5] : [0.3, 0.5, 0.3],
        }}
        transition={{
          duration: 2,
          repeat: Number.POSITIVE_INFINITY,
          repeatType: "reverse",
          delay: index * 0.5,
        }}
      />

      {/* Inner circle */}
      <motion.circle
        cx={x}
        cy={y}
        r={hovered ? 6 : 4}
        fill={index % 2 === 0 ? "#3b82f6" : "#8b5cf6"}
        filter="url(#glow)"
        animate={{
          y: hovered ? [y - 5, y + 5, y - 5] : [y - 2, y + 2, y - 2],
          scale: hovered ? [1, 1.2, 1] : [1, 1.1, 1],
        }}
        transition={{
          duration: 3,
          repeat: Number.POSITIVE_INFINITY,
          repeatType: "reverse",
          delay: index * 0.5,
        }}
        whileHover={{ scale: 1.5 }}
      />

      {/* Tooltip */}
      {hovered && (
        <motion.g
          initial={{ opacity: 0, y: -10 }}
          animate={{ opacity: 1, y: 0 }}
          transition={{ duration: 0.3 }}
        >
          <rect
            x={x - 20}
            y={y - 35}
            width="40"
            height="20"
            rx="4"
            fill="rgba(30, 41, 59, 0.9)"
            stroke="#3b82f6"
            strokeWidth="1"
          />
          <text x={x} y={y - 22} textAnchor="middle" fill="#ffffff" fontSize="10" fontWeight="bold">
            {value}
          </text>
        </motion.g>
      )}
    </motion.g>
  )
}