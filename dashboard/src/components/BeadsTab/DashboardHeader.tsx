import React from 'react';
import { DashboardHeaderProps } from './lib/Types';

import { TABS } from './lib/Constants';

export default function DashboardHeader({
  activeTab,
  setActiveTab,
}: DashboardHeaderProps) {
  return (
    <header className="mb-8">
      <div className="border-b border-gray-700">
        <nav className="mb-px  flex flex-wrap gap-x-6" aria-label="Tabs">
          {TABS.map((tab) => (
            <button
              key={tab.id}
              onClick={() => setActiveTab(tab.id)}
              className={`
                whitespace-nowrap py-4 px-1 border-b-2 font-medium text-sm
                transition-colors duration-200 
                ${
                  activeTab === tab.id
                    ? 'border-blue-500 text-blue-400'
                    : 'border-transparent text-gray-400 hover:text-white hover:border-gray-300'
                }
              `}
              aria-current={activeTab === tab.id ? 'page' : undefined}
            >
              {tab.label}
            </button>
          ))}
        </nav>
      </div>
    </header>
  );
}
