import React, { useState } from 'react';
import {
  Bitcoin,
  Wrench,
  LayoutDashboard,
  Package,
  MemoryStick,
  Layers,
  Menu,
  X,
  Search,
} from 'lucide-react';
import { Page } from '../Dashboard/Types';
import { HeaderNavProps } from './Types';

const NAV_ITEMS = [
  {
    label: 'Installation',
    page: Page.INSTALLATION,
    icon: <Wrench size={18} />,
  },
  {
    label: 'Dashboard',
    page: Page.DASHBOARD,
    icon: <LayoutDashboard size={18} />,
  },
  { label: 'Bead', page: Page.MINER_STATS, icon: <MemoryStick size={18} /> },
  {
    label: 'Inventory',
    page: Page.MINING_INVENTORY,
    icon: <Package size={18} />,
  },
  { label: 'Mempool', page: Page.MEMPOOL, icon: <MemoryStick size={18} /> },
  {
    label: 'Visualize',
    page: Page.DAG_VISUALIZATION,
    icon: <Layers size={18} />,
  },
  {
    label: 'Bitcoin Statistics',
    page: Page.BITCOIN_STATS,
    icon: <Bitcoin size={18} />,
  },
];

const Header: React.FC<HeaderNavProps> = ({
  title = 'Braidpool',
  currentPage,
  setCurrentPage,
}) => {
  const [sidebarOpen, setSidebarOpen] = useState(false);

  return (
    <>
      {/* Header */}
      <header className="fixed top-0 left-0 w-full bg-[#1a1a1a] border-b border-white/10 shadow z-50 h-14 flex items-center">
        <div className="flex items-center justify-between px-4 md:px-6 w-full">
          <div className="flex items-center">
            <div className="w-9 h-9 mr-2 rounded-full overflow-hidden">
              <img
                src="/favicon.ico"
                alt="Logo"
                className="w-full h-full object-cover"
              />
            </div>
            <span className="text-white font-bold text-[1.1rem] tracking-wide mr-2">
              {title}
            </span>

            {/* Mobile Menu Toggle */}
            <button
              className="md:hidden ml-2 p-2 rounded hover:bg-white/10 text-white"
              onClick={() => setSidebarOpen(true)}
            >
              <Menu size={22} />
            </button>

            {/* Desktop Nav */}
            {/* Desktop Nav */}
            <nav className="max-md:hidden md:flex lg:flex ml-25 space-x-1">
              {NAV_ITEMS.map((item) => (
                <button
                  key={item.label}
                  onClick={() => setCurrentPage(item.page)}
                  className={`flex items-center px-3 py-1.5 border-b-2 rounded transition-colors font-medium text-sm
                  ${
                    currentPage === item.page
                      ? 'text-blue-500 border-blue-500 bg-blue-500/10 font-bold'
                      : 'text-white/80 border-transparent hover:bg-blue-500/10'
                  }`}
                >
                  <span className="mr-1.5">{item.icon}</span>
                  {item.label}
                </button>
              ))}
            </nav>
          </div>

          {/* Search Bar */}
          <div className="relative group">
            <span className="absolute left-3 top-1/2 -translate-y-1/2 text-gray-400 group-focus-within:text-blue-500 transition-colors">
              <Search size={18} />
            </span>
            <input
              type="text"
              placeholder="Search Braidpool..."
              className="pl-10 pr-4 py-2 rounded-lg bg-[#232323] text-white placeholder-gray-400 focus:outline-none focus:ring-2 focus:ring-blue-500 focus:bg-[#1f1f1f] hover:bg-[#252525] transition-all duration-200 shadow-sm w-48 md:w-64"
            />
          </div>
        </div>
      </header>

      {/* Sidebar for Mobile */}
      <div
        className={`fixed top-0 left-0 h-full w-64 bg-[#1a1a1a] border-r border-white/10 shadow-lg z-[9999] transform transition-transform duration-300 ${
          sidebarOpen ? 'translate-x-0' : '-translate-x-full'
        } md:hidden`}
      >
        <div className="flex items-center justify-between px-4 h-14 border-b border-white/10">
          <span className="text-white font-bold text-lg">{title}</span>
          <button
            className="p-2 rounded hover:bg-white/10 text-white"
            onClick={() => setSidebarOpen(false)}
          >
            <X size={22} />
          </button>
        </div>
        <nav className="flex flex-col py-4">
          {NAV_ITEMS.map((item) => (
            <button
              key={item.label}
              onClick={() => {
                setCurrentPage(item.page);
                setSidebarOpen(false);
              }}
              className={`flex items-center px-5 py-3 border-l-4 text-left transition-colors font-medium text-base
                ${
                  currentPage === item.page
                    ? 'text-blue-500 border-blue-500 bg-blue-500/10 font-bold'
                    : 'text-white/80 border-transparent hover:bg-blue-500/10'
                }`}
            >
              <span className="mr-2">{item.icon}</span>
              {item.label}
            </button>
          ))}
        </nav>
      </div>
    </>
  );
};

export default Header;
