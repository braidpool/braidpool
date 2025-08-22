import { useState, useEffect, useRef } from 'react';
import DashboardHeader from './DashboardHeader';
import BeadRow from './BeadRow';
import { TrendsTab } from './Trends/TrendsTab';
import { RewardsDashboard } from './Reward/RewardsDashboard';
import { Transaction, Bead, BeadId } from './lib/Types';
import { processBlockData } from './lib/Utils';
import { WEBSOCKET_URLS } from '../../URLs';
import { ITEMS_PER_PAGE, DEFAULT_TIME_RANGE } from './Constants';
import { PoolDominance } from './PoolDominance/PoolDominance';

export default function MinedSharesExplorer() {
  const [expandedBeads, setExpandedBeads] = useState<Record<BeadId, boolean>>({
    bead1: true,
    bead2: false,
  });
  const [activeTab, setActiveTab] = useState('beads');
  const [liveBeads, setLiveBeads] = useState<Bead[]>([]);
  const [activeBead, setActiveBead] = useState<BeadId | null>(null);
  const [wsConnected, setWsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);
  const timeRange = DEFAULT_TIME_RANGE;

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
      <div className="container mx-auto px-2 sm:px-4 py-8">
        <DashboardHeader activeTab={activeTab} setActiveTab={setActiveTab} />

        <div className="relative">
          {activeTab === 'beads' && (
            <div className="space-y-8">
              <div className=" rounded-sm overflow-hidden">
                {/* Table header */}
                <div
                  className="grid max-sm:grid-cols-3 md:grid-cols-5  p-4 border-b text-xs sm:text-sm md:text-base
 gap-4 border-gray-800/80 font-medium"
                >
                  {[
                    'Bead Hash',
                    'Timestamp',
                    'Work',
                    'Transactions',
                    'Rewards',
                  ].map((label) => (
                    <div key={label} className="text-white font-semibold">
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
