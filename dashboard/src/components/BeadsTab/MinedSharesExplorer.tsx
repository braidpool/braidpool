import React, { useState, useEffect } from 'react';
import DashboardHeader from './DashboardHeader';
import BeadRow from './BeadRow';
import { TrendsTab } from './Trends/TrendsTab';
import { RewardsDashboard } from './Reward/RewardsSection';
import { Transaction, Bead } from './lib/types';
import { useWebSocket } from './Hooks/useWebSocket';
import { useChartData } from './Hooks/useChartData';

type BeadId = string;

export default function MinedSharesExplorer() {
   const [expandedBeads, setExpandedBeads] = useState<Record<BeadId, boolean>>({
      bead1: true,
      bead2: false,
    });
    
  const [activeTab, setActiveTab] = useState('beads');
  const [liveBeads, setLiveBeads] = useState<Bead[]>([]);
  const [activeBead, setActiveBead] = useState<BeadId | null>(null);
  const [bitcoinPrice, setBitcoinPrice] = useState<number>(0);
    
  const timeRange = 'month';
  

  const { isConnected: wsConnected } = useWebSocket({
    onMessage: (message) => {
      if (message.type === 'Block_summary') {
        const {
          blockHash,
          height,
          timestamp,
          work,
          txCount,
          reward,
          parent,
          transactions,
        } = message.data;

        const validatedTransactions: Transaction[] = (transactions || []).map(
          (tx: any, index: number) => ({
            id: tx.id || `${blockHash}_tx_${index}`,
            hash: tx.hash || tx.txid || '',
            timestamp: tx.timestamp || timestamp,
            count: tx.count || 0,
            blockId: tx.blockId || height.toString(),
            fee: typeof tx.fee === 'number' ? tx.fee : parseFloat(tx.fee) || 0,
            size: typeof tx.size === 'number' ? tx.size : parseInt(tx.size) || 0,
            feePaid: tx.feePaid || '0',
            feeRate:
              typeof tx.feeRate === 'number'
                ? tx.feeRate
                : parseInt(tx.feeRate) || 0,
            inputs:
              typeof tx.inputs === 'number' ? tx.inputs : parseInt(tx.inputs) || 0,
            outputs:
              typeof tx.outputs === 'number'
                ? tx.outputs
                : parseInt(tx.outputs) || 0,
          })
        );
        
        const difficultyMatch = work ? String(work).match(/(\d+\.?\d*)/) : null;
        const difficulty = difficultyMatch ? parseFloat(difficultyMatch[1]) : 0;

        const newBead: Bead = {
          id: blockHash,
          name: `#${height}`,
          timestamp,
          transactions: txCount,
          difficulty: difficulty,
          reward: typeof reward === 'number' ? reward : parseFloat(reward) || 0,
          parents: parent ? [parent] : [],
          details: validatedTransactions,
        };

        setLiveBeads((prev) => {
          const exists = prev.find((b) => b.id === newBead.id);
          if (exists) return prev;
          return [newBead, ...prev.slice(0, 100)]; 
        });
      } else if (message.type === 'bitcoin_update') {
        const priceData = message.data.price;
        if (priceData && priceData.USD) {
          setBitcoinPrice(parseFloat(priceData.USD));
        }
      }
    },
    onError: (error) => {
      console.error('WebSocket error:', error);
    }
  });

  const toggleBead = (beadId: string) => {
    setExpandedBeads((prev) => ({ ...prev, [beadId]: !prev[beadId] }));
    setActiveBead(beadId);
  };

  const handleParentClick = (hash: string) => {
    navigator.clipboard.writeText(hash).catch(() => {
      console.error('Failed to copy');
    });
  };

  return (
    <div className="min-h-screen bg-[#1c1c1c] text-white relative">
      <div className="container mx-auto px-2 sm:px-4 py-8">
        <DashboardHeader activeTab={activeTab} setActiveTab={setActiveTab} />

        <div className="relative">
          {activeTab === 'beads' && (
            <div className="space-y-8">
              <div className="bg-[#1c1c1c] rounded-sm overflow-hidden">
                {/* Table header */}
                  <div className="grid grid-cols-5 p-4 border-b  text-sm  border-gray-800/80 font-medium">
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
                    <div className="text-gray-400 mb-4">Connecting to server...</div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                ) : liveBeads.length === 0 ? (
                  <div className="p-8 text-center">
                    <div className="text-gray-400 mb-4">Waiting for block data...</div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                ) : (
                  liveBeads.map((bead) => (
                    <BeadRow
                    isActive
                      key={bead.id}
                      bead={bead}
                      isExpanded={!!expandedBeads[bead.id]}
                      onToggle={() => toggleBead(bead.id)}
                      transactions={bead.details || []}
                      onParentClick={handleParentClick}
                    />
                  ))
                )}
              </div>
            </div>
          )}

          {activeTab === 'trends' && <TrendsTab timeRange={timeRange} />}
          {activeTab === 'rewards' && (
            <div className="border border-gray-800/50 rounded-xl p-6 bg-[#1c1c1c]">
              <RewardsDashboard/>
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
