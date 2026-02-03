import { DashboardHeaderProps } from './lib/Types';
import { TABS } from './lib/Constants';

export default function DashboardHeader({
  activeTab,
  setActiveTab,
}: DashboardHeaderProps) {
  return (
    <header>
      <div style={{ borderColor: 'var(--color-border)' }} className="border-b">
        <nav className="mb-px flex flex-wrap gap-x-6" aria-label="Tabs">
          {TABS.map((tab) => (
            <button
              key={tab.id}
              onClick={() => setActiveTab(tab.id)}
              style={{
                color:
                  activeTab === tab.id
                    ? 'var(--color-primary)'
                    : 'var(--color-text-secondary)',
                borderColor:
                  activeTab === tab.id ? 'var(--color-primary)' : 'transparent',
              }}
              className="whitespace-nowrap py-4 px-1 border-b-2 font-medium text-sm transition-colors duration-200 hover:opacity-80"
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
