"use client"

import { useEffect, useRef } from "react"
import type { LogEntry } from "@/lib/types"
import { AlertCircle, CheckCircle, Info } from "lucide-react"

interface VisualLogsProps {
  logs: LogEntry[]
}

export default function VisualLogs({ logs }: VisualLogsProps) {
  const logsEndRef = useRef<HTMLDivElement>(null)

  // Auto-scroll to bottom when new logs arrive
  useEffect(() => {
    if (logsEndRef.current) {
      logsEndRef.current.scrollIntoView({ behavior: "smooth" })
    }
  }, [logs])

  // Get icon based on log type
  const getIcon = (type: string) => {
    switch (type) {
      case "success":
        return <CheckCircle className="h-4 w-4 text-green-400" />
      case "error":
        return <AlertCircle className="h-4 w-4 text-red-400" />
      case "info":
      default:
        return <Info className="h-4 w-4 text-blue-400" />
    }
  }

  // Format timestamp
  const formatTime = (date: Date) => {
    return date.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit", second: "2-digit" })
  }

  return (
    <div className="h-[600px] overflow-y-auto pr-2 space-y-2">
      {logs.length === 0 ? (
        <div className="flex items-center justify-center h-full text-gray-500">No activity yet</div>
      ) : (
        logs.map((log, index) => (
          <div
            key={index}
            className="flex items-start gap-2 p-2 text-sm border border-gray-800 rounded-md bg-gray-800/50"
          >
            {getIcon(log.type)}
            <div className="flex-1 min-w-0">
              <p className="text-gray-200 break-words">{log.message}</p>
              <p className="text-xs text-gray-500">{formatTime(log.timestamp)}</p>
            </div>
          </div>
        ))
      )}
      <div ref={logsEndRef} />
    </div>
  )
}

