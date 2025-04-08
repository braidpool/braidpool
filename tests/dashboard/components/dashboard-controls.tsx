"use client"

import { useState } from "react"
import { Button } from "@/components/ui/button"
import { Slider } from "@/components/ui/slider"
import { Switch } from "@/components/ui/switch"
import { Label } from "@/components/ui/label"
import { Popover, PopoverContent, PopoverTrigger } from "@/components/ui/popover"
import { Settings, RefreshCw, Filter, Download, Share2 } from "lucide-react"
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs"
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from "@/components/ui/select"

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

            <Tabs defaultValue="display" className="w-full">
              <TabsList className="grid grid-cols-2 mb-4 bg-gray-800">
                <TabsTrigger value="display">Display</TabsTrigger>
                <TabsTrigger value="layout">Layout</TabsTrigger>
              </TabsList>

              <TabsContent value="display" className="space-y-4">
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
                  <Label htmlFor="color-scheme" className="text-sm text-gray-400">
                    Color Scheme
                  </Label>
                  <Select defaultValue="default">
                    <SelectTrigger id="color-scheme" className="bg-gray-800 border-gray-700">
                      <SelectValue placeholder="Select color scheme" />
                    </SelectTrigger>
                    <SelectContent className="bg-gray-900 border-gray-700">
                      <SelectItem value="default">Default</SelectItem>
                      <SelectItem value="monochrome">Monochrome</SelectItem>
                      <SelectItem value="colorblind">Colorblind Friendly</SelectItem>
                    </SelectContent>
                  </Select>
                </div>
              </TabsContent>

              <TabsContent value="layout" className="space-y-4">
                <div className="space-y-2">
                  <div className="flex items-center justify-between">
                    <Label htmlFor="max-cohorts" className="text-sm text-gray-400">
                      Max Cohorts: {localFilters.maxCohorts}
                    </Label>
                  </div>
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

                <div className="space-y-2">
                  <Label htmlFor="layout-type" className="text-sm text-gray-400">
                    Layout Type
                  </Label>
                  <Select defaultValue="hierarchical">
                    <SelectTrigger id="layout-type" className="bg-gray-800 border-gray-700">
                      <SelectValue placeholder="Select layout type" />
                    </SelectTrigger>
                    <SelectContent className="bg-gray-900 border-gray-700">
                      <SelectItem value="hierarchical">Hierarchical</SelectItem>
                      <SelectItem value="force-directed">Force Directed</SelectItem>
                      <SelectItem value="radial">Radial</SelectItem>
                    </SelectContent>
                  </Select>
                </div>
              </TabsContent>
            </Tabs>

            <Button onClick={applyFilters} className="w-full bg-blue-600 hover:bg-blue-700">
              Apply Filters
            </Button>
          </div>
        </PopoverContent>
      </Popover>

      <Button variant="outline" size="icon" className="text-gray-400 hover:text-white bg-gray-900 border-gray-700">
        <Download className="h-4 w-4" />
      </Button>

      <Button variant="outline" size="icon" className="text-gray-400 hover:text-white bg-gray-900 border-gray-700">
        <Share2 className="h-4 w-4" />
      </Button>

      <Popover>
        <PopoverTrigger asChild>
          <Button variant="outline" size="icon" className="text-gray-400 hover:text-white bg-gray-900 border-gray-700">
            <Settings className="h-4 w-4" />
          </Button>
        </PopoverTrigger>
        <PopoverContent className="w-80 bg-gray-900 border-gray-700 text-gray-100">
          <div className="space-y-4">
            <h4 className="font-medium text-sm">Dashboard Settings</h4>

            <div className="flex items-center justify-between">
              <Label htmlFor="auto-refresh" className="text-sm text-gray-400">
                Auto-Refresh
              </Label>
              <Switch id="auto-refresh" defaultChecked />
            </div>

            <div className="flex items-center justify-between">
              <Label htmlFor="dark-mode" className="text-sm text-gray-400">
                Dark Mode
              </Label>
              <Switch id="dark-mode" defaultChecked />
            </div>

            <div className="flex items-center justify-between">
              <Label htmlFor="notifications" className="text-sm text-gray-400">
                Notifications
              </Label>
              <Switch id="notifications" defaultChecked />
            </div>

            <div className="flex items-center justify-between">
              <Label htmlFor="animation-speed" className="text-sm text-gray-400">
                Animation Speed
              </Label>
              <Select defaultValue="normal">
                <SelectTrigger id="animation-speed" className="w-24 bg-gray-800 border-gray-700">
                  <SelectValue placeholder="Speed" />
                </SelectTrigger>
                <SelectContent className="bg-gray-900 border-gray-700">
                  <SelectItem value="slow">Slow</SelectItem>
                  <SelectItem value="normal">Normal</SelectItem>
                  <SelectItem value="fast">Fast</SelectItem>
                </SelectContent>
              </Select>
            </div>
          </div>
        </PopoverContent>
      </Popover>
    </div>
  )
}

