import { DashboardHeaderProps } from './lib/Types';
import { TABS } from './lib/Constants';

export default function DashboardHeader({
  activeTab,
  setActiveTab,
}: DashboardHeaderProps) {
  return (
    <header>
      {/* --- Mobile View: Dropdown --- */}
      <div className="block md:!hidden py-4">
        <label htmlFor="tabs" className="sr-only">
          Select a tab
        </label>
        <select
          id="tabs"
          name="tabs"
          className="block w-full rounded-md border border-gray-700 bg-gray-800 py-2 pl-3 pr-3 text-base text-white focus:border-blue-500 focus:outline-none focus:ring-blue-500 sm:text-sm"
          value={activeTab}
          onChange={(e) => setActiveTab(e.target.value)}
        >
          {TABS.map((tab) => (
            <option key={tab.id} value={tab.id}>
              {tab.label}
            </option>
          ))}
        </select>
      </div>

      {/* --- Desktop View: Tabs (Original) --- */}
      <div className="!hidden md:!block border-b border-gray-700">
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