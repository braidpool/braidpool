import { useState, useEffect, useRef, useMemo } from 'react';
import { motion, useAnimation, useInView } from 'framer-motion';
import {
  ArrowUpRight,
  ArrowDownRight,
  Maximize2,
  RefreshCw,
  Download,
} from 'lucide-react';

type TrendType = 'up' | 'down' | 'neutral';

interface ChartDataPoint {
  value: number;
  label: string;
  date: Date;
  formattedDate?: string;
  trend?: TrendType;
}

export default function AdvancedChart({
  data = [],
  height = 300,
  isHovered = false,
  type = 'line',
  showControls = true,
  isLoading = false,
  comparisonData,
  comparisonLabel = 'Comparison',
  timeRange,
}: {
  data: ChartDataPoint[];
  height?: number;
  isHovered?: boolean;
  type?: 'line' | 'bar' | 'area';
  showControls?: boolean;
  isLoading?: boolean;
  comparisonData?: ChartDataPoint[];
  comparisonLabel?: string;
  timeRange: string;
}) {
  const svgRef = useRef<SVGSVGElement>(null);
  const chartControls = useAnimation();
  const isInView = useInView(svgRef, { once: false, amount: 0.3 });
  const [activePoint, setActivePoint] = useState<number | null>(null);
  const [isZoomed, setIsZoomed] = useState(false);
  const [isRefreshing, setIsRefreshing] = useState(false);

  // Generate path from data with safe defaults
  const path = useMemo(() => {
    if (!data || data.length === 0) {
      return 'M0,150 C50,100 100,200 150,150 C200,100 250,200 300,120 C350,60 400,180 450,150 C500,120 550,60 600,120 C650,180 700,120 750,150 C800,180';
    }
    const maxValue = Math.max(...data.map((d) => d.value), 1); // Ensure at least 1
    const xScale = data.length > 1 ? 800 / (data.length - 1) : 0;
    const yScale = height / (maxValue * 1.2);
    return data
      .map((d, i) => {
        const x = i * xScale;
        const y = height - d.value * yScale;
        return i === 0 ? `M${x},${y}` : `L${x},${y}`;
      })
      .join(' ');
  }, [data, height]);

  // Generate comparison path with safe defaults
  const comparisonPath = useMemo(() => {
    if (!comparisonData || comparisonData.length === 0) {
      return '';
    }
    const maxValue = Math.max(...comparisonData.map((d) => d.value), 1);
    const xScale =
      comparisonData.length > 1 ? 800 / (comparisonData.length - 1) : 0;
    const yScale = height / (maxValue * 1.2);
    return comparisonData
      .map((d, i) => {
        const x = i * xScale;
        const y = height - d.value * yScale;
        return i === 0 ? `M${x},${y}` : `L${x},${y}`;
      })
      .join(' ');
  }, [comparisonData, height]);

  // Generate area path for fill
  const areaPath = useMemo(() => {
    return `${path} L800,${height} L0,${height} Z`;
  }, [path, height]);

  // Generate comparison area path for fill
  const comparisonAreaPath = useMemo(() => {
    if (!comparisonPath) return '';
    return `${comparisonPath} L800,${height} L0,${height} Z`;
  }, [comparisonPath, height]);

  // Generate points with guaranteed trend property
  const points = useMemo(() => {
    if (!data || data.length === 0) {
      return [
        {
          x: 150,
          y: 150,
          value: 128,
          label: 'Jan 1',
          date: new Date(),
          formattedDate: 'Jan 1, 2023',
          trend: 'neutral' as const,
        },
        {
          x: 300,
          y: 120,
          value: 156,
          label: 'Jan 15',
          date: new Date(),
          formattedDate: 'Jan 15, 2023',
          trend: 'up' as const,
        },
        {
          x: 450,
          y: 150,
          value: 132,
          label: 'Feb 1',
          date: new Date(),
          formattedDate: 'Feb 1, 2023',
          trend: 'down' as const,
        },
        {
          x: 600,
          y: 120,
          value: 168,
          label: 'Feb 15',
          date: new Date(),
          formattedDate: 'Feb 15, 2023',
          trend: 'up' as const,
        },
        {
          x: 750,
          y: 150,
          value: 142,
          label: 'Mar 1',
          date: new Date(),
          formattedDate: 'Mar 1, 2023',
          trend: 'down' as const,
        },
      ];
    }
    const maxValue = Math.max(...data.map((d) => d.value), 1);
    const xScale = data.length > 1 ? 800 / (data.length - 1) : 0;
    const yScale = height / (maxValue * 1.2);
    return data.map((d, i) => ({
      x: i * xScale,
      y: height - d.value * yScale,
      value: d.value,
      label: d.label,
      date: d.date,
      formattedDate: d.formattedDate || d.date.toLocaleDateString(),
      trend: i > 0 ? (d.value > data[i - 1].value ? 'up' : 'down') : 'neutral',
    }));
  }, [data, height]);

  // Generate comparison points with guaranteed trend property
  const comparisonPoints = useMemo(() => {
    if (!comparisonData || comparisonData.length === 0) {
      return [];
    }
    const maxValue = Math.max(...comparisonData.map((d) => d.value), 1);
    const xScale =
      comparisonData.length > 1 ? 800 / (comparisonData.length - 1) : 0;
    const yScale = height / (maxValue * 1.2);
    return comparisonData.map((d, i) => ({
      x: i * xScale,
      y: height - d.value * yScale,
      value: d.value,
      label: d.label,
      date: d.date,
      formattedDate: d.formattedDate || d.date.toLocaleDateString(),
      trend:
        i > 0
          ? d.value > comparisonData[i - 1].value
            ? 'up'
            : 'down'
          : 'neutral',
    }));
  }, [comparisonData, height]);

  // Animate chart when in view
  useEffect(() => {
    if (isInView) {
      chartControls.start({
        pathLength: 1,
        transition: { duration: 2, ease: 'easeInOut' },
      });
    } else {
      chartControls.start({
        pathLength: 0,
        transition: { duration: 0.5 },
      });
    }
  }, [isInView, chartControls]);

  // Refresh animation
  const handleRefresh = () => {
    setIsRefreshing(true);
    chartControls
      .start({
        pathLength: 0,
        transition: { duration: 0.3 },
      })
      .then(() => {
        chartControls
          .start({
            pathLength: 1,
            transition: { duration: 1.5, ease: 'easeInOut' },
          })
          .then(() => {
            setIsRefreshing(false);
          });
      });
  };

  // Export chart as SVG
  const handleExport = () => {
    if (!svgRef.current) return;
    const svgElement = svgRef.current.cloneNode(true) as SVGElement;
    svgElement.setAttribute('xmlns', 'http://www.w3.org/2000/svg');
    svgElement.setAttribute('width', '800');
    svgElement.setAttribute('height', height.toString());
    const svgString = new XMLSerializer().serializeToString(svgElement);
    const blob = new Blob([svgString], { type: 'image/svg+xml' });
    const link = document.createElement('a');
    link.href = URL.createObjectURL(blob);
    link.download = 'mining-chart.svg';
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
  };

  // Empty state handling
  if (data.length === 0 && !isLoading) {
    return (
      <div className="flex items-center justify-center h-full">
        <div className="text-center text-gray-500">No data available</div>
      </div>
    );
  }

  return (
    <div className="relative w-full h-full">
      {/* Loading overlay */}
      {isLoading && (
        <div className="absolute inset-0 bg-black/30 backdrop-blur-sm flex items-center justify-center z-20">
          <div className="flex flex-col items-center">
            <div className="w-10 h-10 border-4 border-blue-500 border-t-transparent rounded-full animate-spin mb-2"></div>
            <p className="text-blue-300">Loading chart data...</p>
          </div>
        </div>
      )}

      {/* Chart controls */}
      {showControls && (
        <div className="absolute top-0 right-0 flex space-x-2 z-10">
          <motion.button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white"
            whileHover={{
              scale: 1.1,
              backgroundColor: 'rgba(30, 58, 138, 0.5)',
            }}
            whileTap={{ scale: 0.95 }}
            onClick={() => setIsZoomed(!isZoomed)}
            title="Toggle zoom"
          >
            <Maximize2 size={16} />
          </motion.button>
          <motion.button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white"
            whileHover={{
              scale: 1.1,
              backgroundColor: 'rgba(30, 58, 138, 0.5)',
            }}
            whileTap={{ scale: 0.95 }}
            onClick={handleRefresh}
            disabled={isRefreshing}
            title="Refresh chart"
          >
            <RefreshCw
              size={16}
              className={isRefreshing ? 'animate-spin' : ''}
            />
          </motion.button>
          <motion.button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white"
            whileHover={{
              scale: 1.1,
              backgroundColor: 'rgba(30, 58, 138, 0.5)',
            }}
            whileTap={{ scale: 0.95 }}
            onClick={handleExport}
            title="Export chart"
          >
            <Download size={16} />
          </motion.button>
        </div>
      )}

      <motion.div
        animate={{
          height: isZoomed ? '400px' : '100%',
        }}
        transition={{ type: 'spring', stiffness: 300, damping: 30 }}
        className="relative w-full h-full"
      >
        <svg
          className="w-full h-full"
          viewBox={`0 0 800 ${height}`}
          ref={svgRef}
          role="img"
          aria-label="Mining chart"
        >
          <defs>
            <linearGradient id="lineGradient" x1="0%" y1="0%" x2="100%" y2="0%">
              <stop offset="0%" stopColor="#3b82f6" />
              <stop offset="50%" stopColor="#8b5cf6" />
              <stop offset="100%" stopColor="#3b82f6" />
            </linearGradient>
            <linearGradient
              id="comparisonGradient"
              x1="0%"
              y1="0%"
              x2="100%"
              y2="0%"
            >
              <stop offset="0%" stopColor="#10b981" />
              <stop offset="50%" stopColor="#06b6d4" />
              <stop offset="100%" stopColor="#10b981" />
            </linearGradient>
            <linearGradient id="areaGradient" x1="0%" y1="0%" x2="0%" y2="100%">
              <stop offset="0%" stopColor="#3b82f6" stopOpacity="0.5" />
              <stop offset="50%" stopColor="#3b82f6" stopOpacity="0.2" />
              <stop offset="100%" stopColor="#3b82f6" stopOpacity="0" />
            </linearGradient>
            <linearGradient
              id="comparisonAreaGradient"
              x1="0%"
              y1="0%"
              x2="0%"
              y2="100%"
            >
              <stop offset="0%" stopColor="#10b981" stopOpacity="0.3" />
              <stop offset="50%" stopColor="#10b981" stopOpacity="0.1" />
              <stop offset="100%" stopColor="#10b981" stopOpacity="0" />
            </linearGradient>
            <filter id="glow" x="-20%" y="-20%" width="140%" height="140%">
              <feGaussianBlur stdDeviation="6" result="blur" />
              <feComposite in="SourceGraphic" in2="blur" operator="over" />
            </filter>
            <filter id="softGlow" x="-50%" y="-50%" width="200%" height="200%">
              <feGaussianBlur stdDeviation="10" result="blur" />
              <feComposite in="SourceGraphic" in2="blur" operator="over" />
            </filter>
            <linearGradient
              id="animatedGradient"
              x1="0%"
              y1="0%"
              x2="100%"
              y2="0%"
            >
              <stop offset="0%" stopColor="#3b82f6">
                <animate
                  attributeName="stop-color"
                  values="#3b82f6; #8b5cf6; #3b82f6"
                  dur="4s"
                  repeatCount="indefinite"
                />
              </stop>
              <stop offset="50%" stopColor="#8b5cf6">
                <animate
                  attributeName="stop-color"
                  values="#8b5cf6; #3b82f6; #8b5cf6"
                  dur="4s"
                  repeatCount="indefinite"
                />
              </stop>
              <stop offset="100%" stopColor="#3b82f6">
                <animate
                  attributeName="stop-color"
                  values="#3b82f6; #8b5cf6; #3b82f6"
                  dur="4s"
                  repeatCount="indefinite"
                />
              </stop>
            </linearGradient>
            <clipPath id="areaClip">
              <motion.path
                d={areaPath}
                initial={{ pathLength: 0 }}
                animate={chartControls}
              />
            </clipPath>
            <clipPath id="comparisonAreaClip">
              <motion.path
                d={comparisonAreaPath}
                initial={{ pathLength: 0 }}
                animate={chartControls}
              />
            </clipPath>
          </defs>

          {/* Background grid */}
          <g className="opacity-20">
            {Array.from({ length: 5 }).map((_, i) => {
              const y = (i * height) / 4;
              return (
                <motion.line
                  key={`grid-h-${i}`}
                  x1="0"
                  y1={y}
                  x2="800"
                  y2={y}
                  stroke="#4b5563"
                  strokeWidth="1"
                  strokeDasharray="5,5"
                  initial={{ opacity: 0 }}
                  animate={{ opacity: 0.5 }}
                  transition={{ duration: 1, delay: i * 0.1 }}
                />
              );
            })}
            {Array.from({ length: 9 }).map((_, i) => {
              const x = (i * 800) / 8;
              return (
                <motion.line
                  key={`grid-v-${i}`}
                  x1={x}
                  y1="0"
                  x2={x}
                  y2={height}
                  stroke="#4b5563"
                  strokeWidth="1"
                  strokeDasharray="5,5"
                  initial={{ opacity: 0 }}
                  animate={{ opacity: 0.5 }}
                  transition={{ duration: 1, delay: i * 0.05 }}
                />
              );
            })}
          </g>

          {/* X-axis line */}
          <line
            x1="0"
            y1={height}
            x2="800"
            y2={height}
            stroke="#6b7280"
            strokeWidth="1.5"
          />

          {/* Date-aligned grid lines */}
          {points.length > 0 &&
            points.map((point, i) => {
              const date = point.date;
              const isMonthStart = date.getDate() === 1;
              const isWeekStart = date.getDay() === 0;
              let showGridLine = false;
              if (timeRange === 'year' && isMonthStart) {
                showGridLine = true;
              } else if (
                timeRange === 'quarter' &&
                (isMonthStart || isWeekStart)
              ) {
                showGridLine = true;
              } else if (
                (timeRange === 'month' || timeRange === 'week') &&
                isWeekStart
              ) {
                showGridLine = true;
              }
              return showGridLine ? (
                <motion.line
                  key={`date-grid-${i}`}
                  x1={point.x}
                  y1="0"
                  x2={point.x}
                  y2={height}
                  stroke="#4b5563"
                  strokeWidth="1"
                  strokeDasharray="5,5"
                  initial={{ opacity: 0 }}
                  animate={{ opacity: 0.7 }}
                  transition={{ duration: 1, delay: i * 0.05 }}
                />
              ) : null;
            })}

          {/* Add date markers at regular intervals */}
          {points.length > 0 &&
            points.map((point, i) => {
              const showMarker =
                timeRange === 'week'
                  ? true
                  : timeRange === 'month'
                    ? i % 2 === 0
                    : timeRange === 'quarter'
                      ? i % 3 === 0
                      : i % 4 === 0;
              return showMarker ? (
                <line
                  key={`date-marker-${i}`}
                  x1={point.x}
                  y1={height - 5}
                  x2={point.x}
                  y2={height + 5}
                  stroke="#4b5563"
                  strokeWidth="1"
                />
              ) : null;
            })}

          {/* Comparison area under the curve */}
          {comparisonPath && (
            <motion.path
              d={comparisonAreaPath}
              fill="url(#comparisonAreaGradient)"
              initial={{ opacity: 0 }}
              animate={{ opacity: isHovered ? 0.6 : 0.3 }}
              transition={{ duration: 0.5 }}
              clipPath="url(#comparisonAreaClip)"
            />
          )}

          {/* Area under the curve */}
          <motion.path
            d={areaPath}
            fill="url(#areaGradient)"
            initial={{ opacity: 0 }}
            animate={{ opacity: isHovered ? 0.8 : 0.5 }}
            transition={{ duration: 0.5 }}
            clipPath="url(#areaClip)"
          />

          {/* Comparison line */}
          {comparisonPath && (
            <motion.path
              d={comparisonPath}
              fill="none"
              stroke="url(#comparisonGradient)"
              strokeWidth={isHovered ? '3' : '2'}
              strokeLinecap="round"
              strokeLinejoin="round"
              filter="url(#glow)"
              initial={{ pathLength: 0 }}
              animate={chartControls}
            />
          )}

          {/* Main line */}
          <motion.path
            d={path}
            fill="none"
            stroke={isHovered ? 'url(#animatedGradient)' : 'url(#lineGradient)'}
            strokeWidth={isHovered ? '4' : '3'}
            strokeLinecap="round"
            strokeLinejoin="round"
            filter="url(#glow)"
            initial={{ pathLength: 0 }}
            animate={chartControls}
          />

          {/* Main data points along the line */}
          {points.map((point, i) => (
            <motion.g
              key={i}
              onHoverStart={() => setActivePoint(i)}
              onHoverEnd={() => setActivePoint(null)}
            >
              {/* Only show trend indicator if trend exists and isn't neutral */}
              {point.trend && point.trend !== 'neutral' && (
                <motion.circle
                  cx={point.x}
                  cy={point.y - 20}
                  r={12}
                  fill={
                    point.trend === 'up'
                      ? 'rgba(16, 185, 129, 0.2)'
                      : 'rgba(239, 68, 68, 0.2)'
                  }
                  initial={{ scale: 0 }}
                  animate={{ scale: activePoint === i ? 1 : 0 }}
                  transition={{ duration: 0.3 }}
                />
              )}

              <motion.circle
                cx={point.x}
                cy={point.y}
                r={isHovered ? 12 : 8}
                fill={
                  point.trend === 'up'
                    ? 'rgba(16, 185, 129, 0.3)'
                    : 'rgba(59, 130, 246, 0.3)'
                }
                filter="url(#softGlow)"
                animate={{
                  r: isHovered ? [8, 12, 8] : [6, 8, 6],
                  opacity: isHovered ? [0.5, 0.8, 0.5] : [0.3, 0.5, 0.3],
                }}
                transition={{
                  duration: 2,
                  repeat: Number.POSITIVE_INFINITY,
                  repeatType: 'reverse',
                  delay: i * 0.5,
                }}
              />

              <motion.circle
                cx={point.x}
                cy={point.y}
                r={isHovered ? 6 : 4}
                fill={point.trend === 'up' ? '#10b981' : '#3b82f6'}
                filter="url(#glow)"
                animate={{
                  y: isHovered
                    ? [point.y - 5, point.y + 5, point.y - 5]
                    : [point.y - 2, point.y + 2, point.y - 2],
                  scale:
                    activePoint === i
                      ? 1.5
                      : isHovered
                        ? [1, 1.2, 1]
                        : [1, 1.1, 1],
                }}
                transition={{
                  duration: 3,
                  repeat: Number.POSITIVE_INFINITY,
                  repeatType: 'reverse',
                  delay: i * 0.5,
                }}
              />

              {activePoint === i &&
                point.trend &&
                point.trend !== 'neutral' && (
                  <motion.g
                    initial={{ opacity: 0, scale: 0 }}
                    animate={{ opacity: 1, scale: 1 }}
                    transition={{ duration: 0.3 }}
                  >
                    {point.trend === 'up' ? (
                      <ArrowUpRight
                        x={point.x - 6}
                        y={point.y - 26}
                        size={12}
                        className="text-emerald-500"
                      />
                    ) : (
                      <ArrowDownRight
                        x={point.x - 6}
                        y={point.y - 26}
                        size={12}
                        className="text-red-500"
                      />
                    )}
                  </motion.g>
                )}

              {activePoint === i && (
                <motion.g
                  initial={{ opacity: 0, y: -10 }}
                  animate={{ opacity: 1, y: 0 }}
                  transition={{ duration: 0.3 }}
                >
                  <rect
                    x={point.x - 70}
                    y={point.y - 80}
                    width="140"
                    height="60"
                    rx="6"
                    fill="rgba(15, 23, 42, 0.95)"
                    stroke={point.trend === 'up' ? '#10b981' : '#3b82f6'}
                    strokeWidth="1"
                  />
                  <text
                    x={point.x}
                    y={point.y - 60}
                    textAnchor="middle"
                    fill="#ffffff"
                    fontSize="12"
                    fontWeight="bold"
                    fontFamily="Inter, sans-serif"
                  >
                    {point.value.toFixed(1)} BTC
                  </text>
                  <text
                    x={point.x}
                    y={point.y - 40}
                    textAnchor="middle"
                    fill="#ffffff"
                    fontSize="11"
                    fontFamily="Inter, sans-serif"
                  >
                    {point.formattedDate}
                  </text>
                </motion.g>
              )}
            </motion.g>
          ))}

          {/* X-axis date labels */}
          {points.map((point, i) => {
            const showLabel =
              timeRange === 'week'
                ? true
                : timeRange === 'month'
                  ? i % 2 === 0
                  : timeRange === 'quarter'
                    ? i % 3 === 0
                    : i % 4 === 0;
            return showLabel ? (
              <g key={`date-label-${i}`}>
                <text
                  x={point.x}
                  y={height + 20}
                  textAnchor="middle"
                  fill="#ffffff"
                  fontSize="11"
                  fontWeight="medium"
                  fontFamily="Inter, sans-serif"
                  className="date-label"
                >
                  {point.label}
                </text>
                <line
                  x1={point.x}
                  y1={height}
                  x2={point.x}
                  y2={height + 5}
                  stroke="#9ca3af"
                  strokeWidth="1"
                />
              </g>
            ) : null;
          })}

          {/* Prediction line */}
          {isHovered && points.length > 0 && (
            <motion.path
              d={`M${points[points.length - 1]?.x},${points[points.length - 1]?.y} L800,${
                points[points.length - 1]?.y - 20
              }`}
              stroke="#3b82f6"
              strokeWidth="2"
              strokeDasharray="5,5"
              fill="none"
              initial={{ opacity: 0 }}
              animate={{ opacity: 0.7 }}
              transition={{ duration: 0.5 }}
            />
          )}

          {/* Legend */}
          {comparisonPath && (
            <g transform="translate(20, 20)">
              <rect width="15" height="15" fill="url(#lineGradient)" rx="2" />
              <text x="25" y="12" fontSize="12" fill="#ffffff">
                Primary
              </text>
              <rect
                y="25"
                width="15"
                height="15"
                fill="url(#comparisonGradient)"
                rx="2"
              />
              <text x="25" y="37" fontSize="12" fill="#ffffff">
                {comparisonLabel}
              </text>
            </g>
          )}
        </svg>
        <div className="text-center text-gray-400 text-sm mt-6">Date</div>
      </motion.div>
    </div>
  );
}
