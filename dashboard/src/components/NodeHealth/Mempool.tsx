import { MempoolInfo } from './Types';
import { formatBytes } from './Utils';

export default function MempoolPanel({ mempool }: { mempool: MempoolInfo }) {
  const mempoolUsage = (mempool.usage / mempool.maxmempool) * 100;

  return (
    <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
      {/* Stats Card */}
      <div className="bg-[#1e1e1e] border border-gray-700 rounded-lg p-6 backdrop-blur-sm">
        <div className="mb-4">
          <h2 className="text-xl font-semibold text-white">
            Mempool Statistics
          </h2>
        </div>
        <div className="space-y-6">
          <div>
            <div className="flex justify-between text-sm mb-2 text-gray-300">
              <span>Memory Usage</span>
              <span>
                {formatBytes(mempool.usage)} / {formatBytes(mempool.maxmempool)}
              </span>
            </div>
            <div className="w-full h-2 bg-gray-700 rounded">
              <div
                className="h-2 bg-green-500 rounded"
                style={{ width: `${mempoolUsage}%` }}
              />
            </div>
          </div>

          <div className="grid grid-cols-2 gap-4">
            <div>
              <p className="text-sm font-medium text-gray-300">Transactions</p>
              <p className="text-2xl font-bold text-white">
                {mempool.size.toLocaleString()}
              </p>
            </div>
            <div>
              <p className="text-sm font-medium text-gray-300">Min Fee Rate</p>
              <p className="font-mono text-white">
                {mempool.mempoolminfee.toFixed(8)} BTC/kvB
              </p>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
