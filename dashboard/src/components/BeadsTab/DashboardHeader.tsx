import { DashboardHeaderProps } from './lib/Types';
import { TABS } from './lib/Constants';

export default function DashboardHeader({
  activeTab,
  setActiveTab,
}: DashboardHeaderProps) {
  return (
    <header>
      {/* --- Mobile View: Dropdown for Tabs --- */}
      <div className="md:hidden mb-4">
        <label
          htmlFor="dashboard-tab-select"
          className="sr-only"
        >
          Select dashboard tab
        </label>
        <select
          id="dashboard-tab-select"
          className="block w-full rounded-md bg-gray-900 border border-gray-700 px-3 py-2 text-sm text-gray-100 focus:outline-none focus:ring-1 focus:ring-blue-500"
          value={activeTab}
          onChange={(e) => setActiveTab(e.target.value as any)}
        >
          {TABS.map((tab) => (
            <option key={tab.id} value={tab.id}>
              {tab.label}
            </option>
          ))}
        </select>
      </div>
      {/* --- Desktop View: Tabs (Original) --- */}
      <div className="hidden md:block border-b border-gray-700">
        <nav className="mb-px flex flex-wrap gap-x-6" aria-label="Tabs">
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
