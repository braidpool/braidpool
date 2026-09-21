import { Share2 } from 'lucide-react';
import { NetworkPanelProps } from './Types';

export default function NetworkPanel({ network }: NetworkPanelProps) {
  const cards = [
    {
      label: 'Network Status:',
      value: network.networkactive ? 'Active' : 'Inactive',
      badge: true,
    },
    {
      label: 'Protocol Version:',
      value: network.protocolversion,
    },
    {
      label: 'Version:',
      value: network.subversion,
    },
    {
      label: 'Relay Fee:',
      value: `${network.relayfee} BTC`,
    },
  ];

  return (
    <div className="rounded-lg border border-gray-700 bg-[#1e1e1e] p-6">
      <div className="flex items-center gap-2 mb-5">
        <Share2 className="w-4 h-4 text-blue-400" />
        <h2 className="text-lg font-semibold text-white">Network Status</h2>
      </div>

      <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-6 ">
        {cards.map((item) => (
          <div
            key={item.label}
            className="rounded-lg border border-gray-700 p-4"
          >
            <div className="flex items-baseline gap-2">
              <span className="text-gray-500 text-sm">{item.label}</span>

              {item.badge ? (
                <span
                  className={`px-2 py-1 rounded-sm text-sm font-semibold ${
                    network.networkactive
                      ? 'bg-green-600 text-white'
                      : 'bg-red-600 text-white'
                  }`}
                >
                  {item.value}
                </span>
              ) : (
                <span className="font-mono text-sm font-semibold text-white">
                  {item.value}
                </span>
              )}
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}
