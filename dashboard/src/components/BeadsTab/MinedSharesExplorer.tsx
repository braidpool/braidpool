import { useState } from 'react';
import DashboardHeader from './DashboardHeader';
import { PoolDominance } from './PoolDominance/PoolDominance';

export default function MinedSharesExplorer() {
  const [activeTab, setActiveTab] = useState('pool');
  return (
    <div className="min-h-screen  text-white relative">
      <div className="container mx-auto px-2 sm:px-4 py-8">
        <DashboardHeader activeTab={activeTab} setActiveTab={setActiveTab} />
        <div className="relative">
          <div style={{ display: activeTab === 'pool' ? 'block' : 'none' }}>
            <PoolDominance />
          </div>
        </div>
      </div>
    </div>
  );
}
