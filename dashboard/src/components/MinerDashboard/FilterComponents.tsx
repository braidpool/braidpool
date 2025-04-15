

interface FilterBarProps {
  timeRange: string
  setTimeRange: (range: string) => void
}

const TIME_RANGES = [
  { label: "Week", value: "week" },
  { label: "Month", value: "month" },
  { label: "Quarter", value: "quarter" },
  { label: "Year", value: "year" },
]

export function FilterBar({ timeRange, setTimeRange }: FilterBarProps) {
  return (
    <div className="flex gap-2 mb-6">
      {TIME_RANGES.map((range) => (
        <button
          key={range.value}
          className={`px-4 py-2 rounded-lg font-medium transition-colors ${
            timeRange === range.value
              ? "bg-blue-600 text-white shadow"
              : "bg-gray-800 text-blue-200 hover:bg-blue-900/40"
          }`}
          onClick={() => setTimeRange(range.value)}
        >
          {range.label}
        </button>
      ))}
    </div>
  )
}