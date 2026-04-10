import { MempoolInfo } from './Types';
import { formatBytes } from './Utils';

export default function MempoolPanel({ mempool }: { mempool: MempoolInfo }) {
  const mempoolUsage = (mempool.usage / mempool.maxmempool) * 100;

  return (
    <div className="grid grid-cols-1 gap-6 px-4 w-full">
      {/* Stats Card */}
      <div className="bg-cardPaper border border-border rounded-lg p-6 backdrop-blur-sm">
        <div className="mb-4">
          <h2 className="text-xl font-semibold text-textPrimary">
            Mempool Statistics
          </h2>
        </div>
        <div className="space-y-6">
          <div>
            <div className="flex justify-between text-sm mb-2 text-textSecondary">
              <span>Memory Usage</span>
              <span>
                {formatBytes(mempool.usage)} / {formatBytes(mempool.maxmempool)}
              </span>
            </div>
            <div className="w-full h-2 bg-border rounded">
              <div
                className="h-2 bg-green-500 rounded"
                style={{ width: `${mempoolUsage}%` }}
              />
            </div>
          </div>

          <div className="flex justify-between">
            <div>
              <p className="text-sm font-medium text-textSecondary">
                Transactions
              </p>
              <p className="text-2xl font-bold text-textPrimary">
                {mempool.size.toLocaleString()}
              </p>
            </div>
            <div className="text-right">
              <p className="text-sm font-medium text-textSecondary">
                Min Fee Rate
              </p>
              <p className="font-mono text-textPrimary">
                {mempool.mempoolminfee.toFixed(8)} BTC/kvB
              </p>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
