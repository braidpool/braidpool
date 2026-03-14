import { useState } from 'react';
import DashboardHeader from './DashboardHeader';
import { TrendsTab } from './Trends/TrendsTab';
import { RewardsDashboard } from './Reward/RewardsDashboard';
import { DEFAULT_TIME_RANGE } from './Constants';
import { PoolDominance } from './PoolDominance/PoolDominance';
import GraphVisualization from '../BraidPoolDAG/BraidPoolDAG';

export default function MinedSharesExplorer() {
  const [activeTab, setActiveTab] = useState('beads');
  const timeRange = DEFAULT_TIME_RANGE;
  return (
    <div className="min-h-screen  text-white relative">
      <div className="container mx-auto px-2 sm:px-4 py-8">
        <DashboardHeader activeTab={activeTab} setActiveTab={setActiveTab} />
        <div className="relative">
          {activeTab === 'beads' && (
            <div className="space-y-8">
              <GraphVisualization />
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
