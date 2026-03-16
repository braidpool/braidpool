import { useState, useEffect, useRef } from 'react';
import { X } from 'lucide-react';
import DashboardHeader from './DashboardHeader';
import BeadRow from './BeadRow';
import { TrendsTab } from './Trends/TrendsTab';
import { RewardsDashboard } from './Reward/RewardsDashboard';
import { Transaction, Bead, BeadId } from './lib/Types';
import { processBlockData } from './lib/Utils';
import { WEBSOCKET_URLS } from '../../URLs';
import { ITEMS_PER_PAGE, DEFAULT_TIME_RANGE } from './Constants';
import { PoolDominance } from './PoolDominance/PoolDominance';
import { TABS } from './lib/Constants';

export default function MinedSharesExplorer({
  activeTab: propActiveTab,
  setActiveTab: propSetActiveTab,
  isSidebarOpen: propSidebarOpen,
  setIsSidebarOpen: propSetSidebarOpen,
}: {
  activeTab?: string;
  setActiveTab?: (tab: string) => void;
  isSidebarOpen?: boolean;
  setIsSidebarOpen?: (open: boolean) => void;
}) {
  // Support both controlled (via props) and uncontrolled (internal state) modes.
  // This allows the component to work standalone (e.g. /minedsharesexplorer route)
  // while still being controllable by a parent component.
  const [internalActiveTab, setInternalActiveTab] = useState('beads');
  const activeTab =
    propActiveTab !== undefined ? propActiveTab : internalActiveTab;
  const setActiveTab = (tab: string) => {
    if (propSetActiveTab) propSetActiveTab(tab);
    if (propActiveTab === undefined) setInternalActiveTab(tab);
  };

  const [expandedBeads, setExpandedBeads] = useState<Record<BeadId, boolean>>({
    bead1: true,
    bead2: false,
  });
  const [liveBeads, setLiveBeads] = useState<Bead[]>([]);
  const [activeBead, setActiveBead] = useState<BeadId | null>(null);
  const [wsConnected, setWsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);
  const timeRange = DEFAULT_TIME_RANGE;
  const [internalSidebarOpen, setInternalSidebarOpen] = useState(false);
  const isSidebarOpen = propSidebarOpen ?? internalSidebarOpen;
  const setIsSidebarOpen = (open: boolean) => {
    if (propSetSidebarOpen) propSetSidebarOpen(open);
    if (propSidebarOpen === undefined) setInternalSidebarOpen(open);
  };

  // Pagination state
  const itemsPerPage = ITEMS_PER_PAGE;
  const [currentPage, setCurrentPage] = useState(1);

  const totalPages = Math.ceil(liveBeads.length / itemsPerPage);

  const paginatedBeads = liveBeads.slice(
    (currentPage - 1) * itemsPerPage,
    currentPage * itemsPerPage
  );

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    let isMounted = true;
    wsRef.current = ws;

    ws.onopen = () => {
      if (!isMounted) return;
      setWsConnected(true);
    };

    ws.onerror = (error) => {
      setWsConnected(false);
      console.error('WebSocket error:', error);
    };

    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'block_data') {
          const processed = processBlockData(message.data);
          const {
            blockHash,
            height,
            timestamp,
            work,
            txCount,
            reward,
            parent,
            transactions,
          } = processed;

          const validatedTransactions: Transaction[] = (transactions || []).map(
            (tx: any, index: number) => ({
              id: tx.id || `${blockHash}_tx_${index}`,
              hash: tx.hash || tx.txid || '',
              timestamp: tx.timestamp || timestamp,
              count: tx.count || 0,
              blockId: tx.blockId || height.toString(),
              fee:
                typeof tx.fee === 'number' ? tx.fee : parseFloat(tx.fee) || 0,
              size:
                typeof tx.size === 'number' ? tx.size : parseInt(tx.size) || 0,
              feePaid: tx.feePaid || '0',
              feeRate:
                typeof tx.feeRate === 'number'
                  ? tx.feeRate
                  : parseInt(tx.feeRate) || 0,
              inputs:
                typeof tx.inputs === 'number'
                  ? tx.inputs
                  : parseInt(tx.inputs) || 0,
              outputs:
                typeof tx.outputs === 'number'
                  ? tx.outputs
                  : parseInt(tx.outputs) || 0,
            })
          );

          const difficultyMatch = work
            ? String(work).match(/(\d+\.?\d*)/)
            : null;
          const difficulty = difficultyMatch
            ? parseFloat(difficultyMatch[1])
            : 0;

          const newBead: Bead = {
            id: blockHash,
            name: `#${height}`,
            timestamp: new Date(timestamp).toLocaleString('en-IN', {
              day: '2-digit',
              month: '2-digit',
              year: 'numeric',
              hour: '2-digit',
              minute: '2-digit',
              second: '2-digit',
              hour12: false,
            }),
            transactions: txCount,
            difficulty: difficulty,
            reward:
              typeof reward === 'number' ? reward : parseFloat(reward) || 0,
            parents: parent ? [parent] : [],
            details: validatedTransactions,
          };

          setLiveBeads((prev) => {
            const exists = prev.find((b) => b.id === newBead.id);
            if (exists) return prev;
            return [newBead, ...prev.slice(0, 100)];
          });
        }
      } catch (e) {
        console.error('WebSocket message parse error:', e);
      }
    };

    ws.onclose = () => {
      if (!isMounted) return;
      console.log('WebSocket disconnected');
      setWsConnected(false);
    };

    return () => {
      isMounted = false;
      ws.onopen = null;
      ws.onclose = null;
      ws.onerror = null;
      ws.onmessage = null;
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, []);
  const toggleBead = (beadId: string) => {
    setExpandedBeads((prev) => ({ ...prev, [beadId]: !prev[beadId] }));
    setActiveBead(beadId);
  };

  return (
    <div className="min-h-screen  text-white relative">
      {/* Mobile sidebar backdrop */}
      {isSidebarOpen && (
        <div
          className="sm:hidden fixed inset-x-0 top-16 bottom-0 z-40 bg-black/50"
          onClick={() => setIsSidebarOpen(false)}
        />
      )}

      {/* Mobile sidebar drawer */}
      <aside
        className={`sm:hidden fixed top-16 left-0 z-50 h-[calc(100vh-4rem)] w-52 bg-gray-900 border-r border-gray-800/80 p-4 flex flex-col transition-transform duration-200 ease-in-out ${
          isSidebarOpen ? 'translate-x-0' : '-translate-x-full'
        }`}
      >
        <div className="flex items-center justify-between mb-4">
          <span className="text-xs font-semibold uppercase tracking-wide text-gray-400">
            Views
          </span>
          <button
            onClick={() => setIsSidebarOpen(false)}
            className="p-1 rounded-md text-gray-400 hover:text-white hover:bg-gray-800 transition-colors"
            aria-label="Close sidebar"
          >
            <X size={16} />
          </button>
        </div>
        <nav className="space-y-1">
          {TABS.map((tab) => {
            const isActive = activeTab === tab.id;
            return (
              <button
                key={tab.id}
                onClick={() => {
                  setActiveTab(tab.id);
                  setIsSidebarOpen(false);
                }}
                className={`flex w-full items-center justify-between rounded-lg px-3 py-2.5 text-sm transition-colors border ${
                  isActive
                    ? 'border-blue-500/60 bg-blue-500/10 text-white shadow-[0_0_0_1px_rgba(59,130,246,0.35)]'
                    : 'border-transparent text-gray-300 hover:text-white hover:border-gray-700 hover:bg-gray-800/80'
                }`}
                aria-current={isActive ? 'page' : undefined}
              >
                <span className="text-left leading-tight">{tab.label}</span>
                {isActive && (
                  <span
                    className="h-2 w-2 rounded-full bg-blue-400"
                    aria-hidden
                  />
                )}
              </button>
            );
          })}
        </nav>
      </aside>

      <div className="container mx-auto px-2 sm:px-4 py-8">
        <DashboardHeader activeTab={activeTab} setActiveTab={setActiveTab} />

        <div className="relative">
          {activeTab === 'beads' && (
            <div className="space-y-8">
              <div className=" rounded-sm overflow-hidden">
                {/* Table header */}
                <div
                  className="grid max-md:grid-cols-3 md:grid-cols-5  p-4 border-b text-xs sm:text-sm md:text-base
 gap-4 border-gray-800/80 font-medium"
                >
                  {[
                    { label: 'Bead Hash' },
                    { label: 'Timestamp' },
                    { label: 'Work' },
                    { label: 'Transactions', className: 'max-md:hidden' },
                    { label: 'Rewards', className: 'max-md:hidden' },
                  ].map(({ label, className }) => (
                    <div
                      key={label}
                      className={`text-white font-semibold ${className || ''}`}
                    >
                      {label}
                    </div>
                  ))}
                </div>

                {!wsConnected ? (
                  <div className="p-8 text-center">
                    <div className="text-gray-400 mb-4">
                      Connecting to server...
                    </div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                ) : paginatedBeads.length === 0 ? (
                  <div className="p-8 text-center">
                    <div className="text-gray-400 mb-4">
                      Waiting for block data...
                    </div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                ) : (
                  paginatedBeads.map((bead) => (
                    <BeadRow
                      key={bead.id}
                      isActive={activeBead === bead.id}
                      bead={bead}
                      isExpanded={!!expandedBeads[bead.id]}
                      onToggle={() => toggleBead(bead.id)}
                      transactions={bead.details || []}
                    />
                  ))
                )}
              </div>

              {/* Pagination */}
              {totalPages > 1 && (
                <div className="w-full flex justify-center mt-4 ">
                  <div className="flex items-center gap-4 ">
                    <button
                      disabled={currentPage === 1}
                      onClick={() => setCurrentPage((prev) => prev - 1)}
                      className={`px-3 py-1 rounded-md ${
                        currentPage === 1
                          ? 'bg-gray-700 text-gray-400 cursor-not-allowed'
                          : 'bg-gray-800 hover:bg-gray-700'
                      }`}
                    >
                      Previous
                    </button>
                    <span className="text-sm">
                      Page {currentPage} of {totalPages}
                    </span>
                    <button
                      disabled={currentPage === totalPages}
                      onClick={() => setCurrentPage((prev) => prev + 1)}
                      className={`px-3 py-1 rounded-md ${
                        currentPage === totalPages
                          ? 'bg-gray-700 text-gray-400 cursor-not-allowed'
                          : 'bg-gray-800 hover:bg-gray-700'
                      }`}
                    >
                      Next
                    </button>
                  </div>
                </div>
              )}
            </div>
          )}
          <div style={{ display: activeTab === 'trends' ? 'block' : 'none' }}>
            <TrendsTab timeRange={timeRange} />
          </div>
          <div
            style={{ display: activeTab === 'rewards' ? 'block' : 'none' }}
            className="border border-gray-800/50 rounded-xl p-6"
          >
            <RewardsDashboard />
          </div>
          <div style={{ display: activeTab === 'pool' ? 'block' : 'none' }}>
            <PoolDominance />
          </div>
        </div>
      </div>
    </div>
  );
}
