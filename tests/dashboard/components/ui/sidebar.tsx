"use client"

import * as React from "react"
import { cn } from "@/lib/utils"
import { Button } from "@/components/ui/button"
import { Sheet, SheetContent } from "@/components/ui/sheet"

const SIDEBAR_WIDTH = "16rem"
const SIDEBAR_WIDTH_MOBILE = "18rem"

type SidebarContext = {
  open: boolean
  toggleSidebar: () => void
}

const SidebarContext = React.createContext<SidebarContext | null>(null)

function useSidebar() {
  const context = React.useContext(SidebarContext)
  if (!context) {
    throw new Error("useSidebar must be used within a SidebarProvider.")
  }
  return context
}

const SidebarProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const [open, setOpen] = React.useState(true)

  const toggleSidebar = React.useCallback(() => {
    setOpen((prev) => !prev)
  }, [])

  const contextValue = React.useMemo(() => ({ open, toggleSidebar }), [open, toggleSidebar])

  return (
    <SidebarContext.Provider value={contextValue}>
      <div
        style={{ "--sidebar-width": SIDEBAR_WIDTH } as React.CSSProperties}
        className={cn("flex min-h-screen")}
      >
        {children}
      </div>
    </SidebarContext.Provider>
  )
}

const Sidebar: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const { open } = useSidebar()

  return (
    <div
      className={cn(
        "flex flex-col bg-gray-900 text-white transition-all",
        open ? "w-[--sidebar-width]" : "w-0"
      )}
    >
      {children}
    </div>
  )
}

const SidebarTrigger: React.FC = () => {
  const { toggleSidebar } = useSidebar()

  return (
    <Button
      variant="ghost"
      size="icon"
      onClick={toggleSidebar}
      className="absolute top-4 left-4"
    >
      Toggle
    </Button>
  )
}

const SidebarContent: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  return <div className="p-4">{children}</div>
}

const SidebarMobile: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const { open, toggleSidebar } = useSidebar()

  return (
    <Sheet open={open} onOpenChange={toggleSidebar}>
      <SheetContent
        className="w-[--sidebar-width-mobile] bg-gray-900 text-white"
        style={{ "--sidebar-width-mobile": SIDEBAR_WIDTH_MOBILE } as React.CSSProperties}
      >
        {children}
      </SheetContent>
    </Sheet>
  )
}

export { SidebarProvider, Sidebar, SidebarTrigger, SidebarContent, SidebarMobile }
