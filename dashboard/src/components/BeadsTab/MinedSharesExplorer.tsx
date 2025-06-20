import React, { useState, useEffect } from 'react';
import DashboardHeader from './DashboardHeader';

import BeadRow from './BeadRow';
import { BEADS, TRANSACTIONS ,BeadId } from './lib/constants';
import { TrendsTab } from './Trends/TrendsTab';
import { RewardsDashboard } from './Reward/RewardsSection';

export default function MinedSharesExplorer() {
  const [expandedBeads, setExpandedBeads] = useState<Record<BeadId, boolean>>({
    bead1: true,
    bead2: false,
  });
  const [isLoaded, setIsLoaded] = useState(false);
  const [activeBead, setActiveBead] = useState<BeadId | null>(null);
  const [activeTab, setActiveTab] = useState('beads');
  const timeRange= 'month'

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
const handleParentClick = (hash: string) => {
  navigator.clipboard.writeText(hash).catch(() => {
    console.error('Failed to copy');
  });
};



  return (
    <div className="min-h-screen bg-[#1c1c1c] text-white relative">
      <div className="container mx-auto px-4 py-8">
        <DashboardHeader activeTab={activeTab} setActiveTab={setActiveTab} />

        <div className="relative">
          {activeTab === 'beads' && (
            <div className="space-y-8">
              <div className="  bg-[#1c1c1c]  rounded-sm overflow-hidden">
                {/* Table header */}
                <div className="grid grid-cols-5 p-4 border-b  border-gray-800/80 font-medium">
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
                      isExpanded={expandedBeads[bead.id]}
                      onToggle={() => toggleBead(bead.id)}
                      isActive={activeBead === (bead.id)}
                      transactions={TRANSACTIONS[bead.id] || []}
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
              <RewardsDashboard />
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
