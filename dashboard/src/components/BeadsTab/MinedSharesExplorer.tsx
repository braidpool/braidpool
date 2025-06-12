import React, { useState, useEffect } from 'react';
import DashboardHeader from './DashboardHeader';
import EnhancedBlocksTab from './BlockVisulisation/Block';
import BeadRow from './BeadRow';
import { BEADS, TRANSACTIONS } from './lib/constants';
import { TrendsTab } from './Trends/TrendsTab';
import { RewardsDashboard } from './Reward/RewardsSection';

type BeadId = 'bead1' | 'bead2';

export default function MinedSharesExplorer() {
  const [expandedBeads, setExpandedBeads] = useState<Record<BeadId, boolean>>({
    bead1: true,
    bead2: false,
  });
  const [isLoaded, setIsLoaded] = useState(false);
  const [activeBead, setActiveBead] = useState<BeadId | null>(null);
  const [activeTab, setActiveTab] = useState('beads');
  const [timeRange] = useState('month');

  useEffect(() => {
    const timer = setTimeout(() => setIsLoaded(true), 1000);
    return () => clearTimeout(timer);
  }, []);

  const toggleBead = (beadId: BeadId) => {
    setExpandedBeads((prev) => ({
      ...prev,
      [beadId]: !prev[beadId],
    }));
    setActiveBead(beadId);
  };

  const handleParentClick = (parentHash: string) => {
     navigator.clipboard.writeText(parentHash)
    .then(() => {
      console.log(`Parent hash copied to clipboard:\n${parentHash}`);
    })
    .catch(() => {
      console.log('Failed to copy parent hash.');
    });
    
  };

  return (
    <div className="min-h-screen bg-black text-white relative">
      <div className="container mx-auto px-4 py-8">
        <DashboardHeader
          headerOpacity={1}
          headerScale={1}
          activeTab={activeTab}
          setActiveTab={setActiveTab}
        />

        <div className="relative">
          {activeTab === 'beads' && (
            <div className="space-y-8">
              <div className=" mb-8 bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm overflow-hidden">
                {/* Table header */}
                <div className="grid grid-cols-5 p-4 border-b  border-gray-800/80 font-medium">
                  {[
                    'Bead Hash',
                    'Timestamp',
                    'Work',
                    'Transactions',
                    'Rewards',
                  ].map((label) => (
                    <div key={label} className="text-blue-200 font-semibold">
                      {label}
                    </div>
                  ))}
                </div>

                {!isLoaded ? (
                  <div className="p-8">
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                ) : (
                  BEADS.map((bead) => (
                    <BeadRow
                      key={bead.id}
                      bead={bead}
                      isExpanded={!!expandedBeads[bead.id as BeadId]}
                      onToggle={() => toggleBead(bead.id as BeadId)}
                      isActive={activeBead === (bead.id as BeadId)}
                      transactions={TRANSACTIONS[bead.id as BeadId] || []}
                      onParentClick={handleParentClick}
                    />
                  ))
                )}
              </div>
            </div>
          )}

          {activeTab === 'trends' && <TrendsTab timeRange={timeRange} />}
          {activeTab === 'blocks' && (
            <div className="border border-gray-800/50 rounded-xl p-6 bg-black/30">
              <EnhancedBlocksTab timeRange={timeRange} />
            </div>
          )}
          {activeTab === 'rewards' && <RewardsDashboard />}
        </div>
      </div>
    </div>
  );
}
