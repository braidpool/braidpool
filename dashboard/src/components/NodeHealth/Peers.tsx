import { PeerInfo } from './__tests__/types';

const formatBytes = (bytes: number) => {
  const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];
  if (bytes === 0) return '0 B';
  const i = Math.floor(Math.log(bytes) / Math.log(1024));
  return Math.round((bytes / Math.pow(1024, i)) * 100) / 100 + ' ' + sizes[i];
};

interface PeersPanelProps {
  peers: PeerInfo[];
}

export default function Peers({ peers }: PeersPanelProps) {
  return (
    <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm shadow-md">
      <div className="px-6 py-4 border-b border-gray-700">
        <h2 className="text-white text-xl font-semibold">Connected Peers</h2>
        <p className="text-gray-300 text-sm">
          {peers.length} total peers connected
        </p>
      </div>
      <div className="px-6 py-4 space-y-4">
        {peers.map((peer) => (
          <div
            key={peer.id}
            className="flex items-center justify-between p-4 border border-gray-700 rounded-lg bg-gray-900/30 hover:bg-gray-900/50 transition-colors"
          >
            <div className="space-y-1">
              <p className="text-white font-medium">{peer.addr}</p>
              <div className="flex items-center gap-2">
                <span
                  className={`px-2 py-0.5 rounded-full text-xs font-medium 
                    ${
                      peer.inbound
                        ? 'bg-gray-600 text-gray-200'
                        : 'bg-blue-600 text-white'
                    }`}
                >
                  {peer.inbound ? 'Inbound' : 'Outbound'}
                </span>
                <span className="text-sm text-gray-400">{peer.subver}</span>
              </div>
            </div>

            <div className="text-right space-y-1">
              <p className="text-sm font-medium text-white">
                Ping: {peer.ping}ms
              </p>
              <p className="text-xs text-gray-400">
                ↑ {formatBytes(peer.bytessent)} ↓ {formatBytes(peer.bytesrecv)}
              </p>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}
