import { BarChart3, Layers, Cpu, Database, Bitcoin } from 'lucide-react';

export default function DashboardHeader({
  activeTab,
  setActiveTab,
}: {
  activeTab: string;
  setActiveTab: (tab: string) => void;
}) {
  return (
    <div className=" top-0 z-50 pt-4 pb-6 backdrop-blur-md bg-[#1c1c1c] rounded-sm ">
      <div className="flex flex-col md:flex-row justify-between items-start md:items-center gap-4">
        <div className="w-full md:w-auto ">
          <h1 className="text-xl sm:text-xl md:text-3xl font-bold bg-clip-text  text-white tracking-tight">
            Beads Explorer
          </h1>

          <div className="flex gap-3 md:w-auto justify-end ">
            <button className="relative px-3 sm:px-4 py-2 rounded-lg text-white text-sm sm:text-base font-medium overflow-hidden  bg-gray-700 hover:bg-black ">
              <span className="relative z-10 flex items-center justify-center gap-2">
                <BarChart3 className="w-4 h-4" />
                <span className="">Analytics</span>
              </span>
            </button>
            <button className="relative px-3 sm:px-4 py-2 rounded-lg text-white text-sm sm:text-base font-medium overflow-hidden   bg-gray-700 hover:bg-black">
              <span className="relative z-10 flex items-center justify-center gap-2">
                <Database className="w-4 h-4" />
                <span className="">Export Data</span>
              </span>
            </button>
          </div>
        </div>
      </div>

      {/* Tab navigation */}
      <div className="flex border-b border-gray-800/70 overflow-x-auto pb-1 scrollbar-hide">
        {[
          {
            id: 'beads',
            label: 'Beads',
            icon: <Cpu className="w-4 h-4" />,
          },
          {
            id: 'trends',
            label: 'Trends',
            icon: <BarChart3 className="w-4 h-4" />,
          },
          {
            id: 'blocks',
            label: 'Blocks',
            icon: <Layers className="w-4 h-4" />,
          },
          {
            id: 'rewards',
            label: 'Rewards',
            icon: <Bitcoin className="w-4 h-4" />,
          },
        ].map((tab) => (
          <button
            key={tab.id}
            className={`flex items-center gap-1 sm:gap-2 px-3 sm:px-4 py-3 font-medium relative whitespace-nowrap text-sm sm:text-base ${
              activeTab === tab.id
                ? 'text-blue-400 border-b-2 border-blue-500'
                : 'text-gray-400 hover:text-gray-200'
            }`}
            onClick={() => setActiveTab(tab.id)}
          >
            {tab.icon}
            {tab.label}
          </button>
        ))}
      </div>
    </div>
  );
}
