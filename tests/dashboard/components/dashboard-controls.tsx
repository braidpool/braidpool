"use client"

import { useState } from "react"
import { Button } from "@/components/ui/button"
import { Slider } from "@/components/ui/slider"
import { Switch } from "@/components/ui/switch"
import { Label } from "@/components/ui/label"
import { Popover, PopoverContent, PopoverTrigger } from "@/components/ui/popover"
import { RefreshCw, Filter } from "lucide-react"

interface DashboardControlsProps {
  filterOptions: {
    showPoolMinedOnly: boolean
    maxCohorts: number
    highlightHighestWorkPath: boolean
  }
  onFilterChange: (newFilters: typeof filterOptions) => void
  onRefresh: () => void
  isLoading: boolean
}

export default function DashboardControls({
  filterOptions,
  onFilterChange,
  onRefresh,
  isLoading,
}: DashboardControlsProps) {
  const [localFilters, setLocalFilters] = useState(filterOptions)

  const handleFilterChange = (key: keyof typeof filterOptions, value: any) => {
    const newFilters = { ...localFilters, [key]: value }
    setLocalFilters(newFilters)
  }

  const applyFilters = () => {
    onFilterChange(localFilters)
  }

  return (
    <div className="flex items-center gap-2">
      <Button
        variant="outline"
        size="sm"
        onClick={onRefresh}
        disabled={isLoading}
        className="text-gray-400 hover:text-white bg-gray-900 border-gray-700"
      >
        <RefreshCw className={`h-4 w-4 mr-2 ${isLoading ? "animate-spin" : ""}`} />
        Refresh
      </Button>

      <Popover>
        <PopoverTrigger asChild>
          <Button variant="outline" size="sm" className="text-gray-400 hover:text-white bg-gray-900 border-gray-700">
            <Filter className="h-4 w-4 mr-2" />
            Filters
          </Button>
        </PopoverTrigger>
        <PopoverContent className="w-80 bg-gray-900 border-gray-700 text-gray-100">
          <div className="space-y-4">
            <h4 className="font-medium text-sm">Visualization Filters</h4>

            <div className="space-y-4">
              <div className="flex items-center justify-between">
                <Label htmlFor="pool-mined-only" className="text-sm text-gray-400">
                  Show Pool-Mined Only
                </Label>
                <Switch
                  id="pool-mined-only"
                  checked={localFilters.showPoolMinedOnly}
                  onCheckedChange={(checked) => handleFilterChange("showPoolMinedOnly", checked)}
                />
              </div>

              <div className="flex items-center justify-between">
                <Label htmlFor="highlight-path" className="text-sm text-gray-400">
                  Highlight Highest Work Path
                </Label>
                <Switch
                  id="highlight-path"
                  checked={localFilters.highlightHighestWorkPath}
                  onCheckedChange={(checked) => handleFilterChange("highlightHighestWorkPath", checked)}
                />
              </div>

              <div className="space-y-2">
                <Label htmlFor="max-cohorts" className="text-sm text-gray-400">
                  Max Cohorts: {localFilters.maxCohorts}
                </Label>
                <Slider
                  id="max-cohorts"
                  min={1}
                  max={20}
                  step={1}
                  value={[localFilters.maxCohorts]}
                  onValueChange={(value) => handleFilterChange("maxCohorts", value[0])}
                  className="py-2"
                />
              </div>
            </div>

            <Button onClick={applyFilters} className="w-full bg-blue-600 hover:bg-blue-700">
              Apply Filters
            </Button>
          </div>
        </PopoverContent>
      </Popover>
    </div>
  )
}

