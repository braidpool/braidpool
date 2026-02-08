import React, { useState, useEffect } from 'react';
import {
  Bitcoin,
  LayoutDashboard,
  Package,
  MemoryStick,
  Layers,
  Menu,
  X,
  HeartPulse,
  Sun,
  Moon,
  Sunset,
} from 'lucide-react';
import { Page } from '../Dashboard/Types';
import { HeaderNavProps } from './Types';
import { ThemeType } from '../../theme/colors';

const NAV_ITEMS = [
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
  {
    label: 'Node Health',
    page: Page.NODE_HEALTH,
    icon: <HeartPulse size={18} />,
  },
];

const MOBILE_BREAKPOINT = 768;

const Header: React.FC<HeaderNavProps> = ({
  title = 'Braidpool',
  currentPage,
  setCurrentPage,
  currentTheme,
  setCurrentTheme,
}) => {
  const [sidebarOpen, setSidebarOpen] = useState(false);
  const [isMobile, setIsMobile] = useState(false);

  useEffect(() => {
    const checkMobile = () => {
      setIsMobile(window.innerWidth < MOBILE_BREAKPOINT);
    };
    checkMobile();
    window.addEventListener('resize', checkMobile);
    return () => window.removeEventListener('resize', checkMobile);
  }, []);

  const cycleTheme = () => {
    const themes: ThemeType[] = ['dark', 'light', 'solarized'];
    const next = (themes.indexOf(currentTheme) + 1) % themes.length;
    setCurrentTheme(themes[next]);
  };

  const ThemeIcon = () => {
    if (currentTheme === 'light') return <Sun size={18} />;
    if (currentTheme === 'solarized') return <Sunset size={18} />;
    return <Moon size={18} />;
  };

  return (
    <>
      <header
        className="fixed top-0 left-0 w-full h-14 z-50 shadow"
        style={{
          backgroundColor: 'var(--color-header-background)',
          borderBottom: '1px solid var(--color-border)',
        }}
      >
        <div className="flex items-center justify-between h-full px-4">
          {/* Logo */}
          <div className="flex items-center gap-2">
            <div className="w-9 h-9 rounded-full overflow-hidden">
              <img
                src="/favicon.ico"
                alt="Logo"
                className="w-full h-full object-cover"
              />
            </div>
            <span
              style={{ color: 'var(--color-text-primary)' }}
              className="font-bold text-lg tracking-wide"
            >
              {title}
            </span>
          </div>

          {/* Desktop Navigation - shows on larger screens */}
          {!isMobile && (
            <div className="flex items-center gap-1">
              {NAV_ITEMS.map((item) => (
                <button
                  key={item.label}
                  onClick={() => setCurrentPage(item.page)}
                  aria-label={`Navigate to ${item.label}`}
                  className="flex items-center px-3 py-1.5 text-sm font-medium rounded transition-colors"
                  style={{
                    color:
                      currentPage === item.page
                        ? 'var(--color-primary)'
                        : 'var(--color-text-secondary)',
                    backgroundColor:
                      currentPage === item.page
                        ? 'var(--color-primary-soft)'
                        : 'transparent',
                    borderBottom:
                      currentPage === item.page
                        ? '2px solid var(--color-primary)'
                        : '2px solid transparent',
                  }}
                  onMouseEnter={(e) => {
                    if (currentPage !== item.page) {
                      e.currentTarget.style.backgroundColor =
                        'var(--color-primary-soft)';
                      e.currentTarget.style.color = 'var(--color-text-primary)';
                    }
                  }}
                  onMouseLeave={(e) => {
                    if (currentPage !== item.page) {
                      e.currentTarget.style.backgroundColor = 'transparent';
                      e.currentTarget.style.color =
                        'var(--color-text-secondary)';
                    }
                  }}
                >
                  <span className="mr-1.5">{item.icon}</span>
                  {item.label}
                </button>
              ))}

              {/* Theme Toggle */}
              <div className="ml-4 pl-4 flex items-center">
                <button
                  onClick={cycleTheme}
                  className="p-1.5 rounded transition-colors"
                  style={{ color: 'var(--color-text-primary)' }}
                  aria-label="Switch theme"
                  onMouseEnter={(e) => {
                    e.currentTarget.style.backgroundColor =
                      'var(--color-primary-soft)';
                  }}
                  onMouseLeave={(e) => {
                    e.currentTarget.style.backgroundColor = 'transparent';
                  }}
                >
                  <ThemeIcon />
                </button>
              </div>
            </div>
          )}

          {/* Mobile Controls - shows on smaller screens */}
          {isMobile && (
            <div className="flex items-center gap-2">
              <button
                onClick={cycleTheme}
                className="p-2 rounded transition-colors"
                style={{ color: 'var(--color-text-primary)' }}
                aria-label="Switch theme"
              >
                <ThemeIcon />
              </button>
              <button
                onClick={() => setSidebarOpen(true)}
                className="p-2 rounded transition-colors"
                style={{ color: 'var(--color-text-primary)' }}
                aria-label="Open navigation menu"
              >
                <Menu size={22} />
              </button>
            </div>
          )}
        </div>
      </header>

      {/* Mobile Sidebar */}
      {isMobile && (
        <div
          className="fixed top-0 left-0 h-full w-64 z-[9999] transition-transform duration-300"
          style={{
            backgroundColor: 'var(--color-header-background)',
            borderRight: '1px solid var(--color-border)',
            boxShadow: '4px 0 15px rgba(0,0,0,0.2)',
            transform: sidebarOpen ? 'translateX(0)' : 'translateX(-100%)',
          }}
        >
          <div
            className="flex items-center justify-between px-4 h-14"
            style={{ borderBottom: '1px solid var(--color-border)' }}
          >
            <span
              style={{ color: 'var(--color-text-primary)' }}
              className="font-bold text-lg"
            >
              {title}
            </span>
            <button
              onClick={() => setSidebarOpen(false)}
              className="p-2 rounded transition-colors"
              style={{ color: 'var(--color-text-primary)' }}
              aria-label="Close navigation menu"
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
                aria-label={`Navigate to ${item.label}`}
                className="flex items-center px-5 py-3 text-base font-medium transition-colors"
                style={{
                  color:
                    currentPage === item.page
                      ? 'var(--color-primary)'
                      : 'var(--color-text-secondary)',
                  backgroundColor:
                    currentPage === item.page
                      ? 'var(--color-primary-soft)'
                      : 'transparent',
                  borderLeft:
                    currentPage === item.page
                      ? '4px solid var(--color-primary)'
                      : '4px solid transparent',
                }}
              >
                <span className="mr-2">{item.icon}</span>
                {item.label}
              </button>
            ))}
          </nav>
        </div>
      )}

      {/* Backdrop overlay when sidebar is open */}
      {isMobile && sidebarOpen && (
        <div
          className="fixed inset-0 z-[9998]"
          style={{ backgroundColor: 'rgba(0,0,0,0.5)' }}
          onClick={() => setSidebarOpen(false)}
        />
      )}
    </>
  );
};

export default Header;
