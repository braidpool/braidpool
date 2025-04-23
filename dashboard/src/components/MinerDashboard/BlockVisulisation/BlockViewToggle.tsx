import {
  Activity,
  BarChart3,
  Layers,
} from "lucide-react"
export function BlockViewToggle({
    viewMode,
    setViewMode,
  }: {
    viewMode: "list" | "grid" | "timeline"
    setViewMode: (mode: "list" | "grid" | "timeline") => void
  }) {
    return (
      <div className="flex items-center gap-3">
        <div className="bg-gray-900/50 rounded-lg p-1 flex">
          <button
            className={`px-3 py-1.5 rounded-md flex items-center gap-1.5 text-sm font-medium transition-colors ${
              viewMode === "list" ? "bg-blue-600/30 text-blue-200" : "text-gray-400 hover:text-white"
            }`}
            onClick={() => setViewMode("list")}
          >
            <BarChart3 className="h-4 w-4" />
            List
          </button>
          <button
            className={`px-3 py-1.5 rounded-md flex items-center gap-1.5 text-sm font-medium transition-colors ${
              viewMode === "grid" ? "bg-blue-600/30 text-blue-200" : "text-gray-400 hover:text-white"
            }`}
            onClick={() => setViewMode("grid")}
          >
            <Layers className="h-4 w-4" />
            Grid
          </button>
          <button
            className={`px-3 py-1.5 rounded-md flex items-center gap-1.5 text-sm font-medium transition-colors ${
              viewMode === "timeline" ? "bg-blue-600/30 text-blue-200" : "text-gray-400 hover:text-white"
            }`}
            onClick={() => setViewMode("timeline")}
          >
            <Activity className="h-4 w-4" />
            Timeline
          </button>
        </div>
      </div>
    )
  }
  