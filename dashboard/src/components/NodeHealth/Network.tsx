import { NetworkPanelProps } from './Types';

export default function NetworkPanel({ network }: NetworkPanelProps) {
  return (
    <div className="grid grid-cols-1 gap-6 px-4 w-full">
      <div className="bg-cardPaper border border-border rounded-xl backdrop-blur-sm p-6">
        <h2 className="text-textPrimary text-lg font-semibold mb-4">
          Network Status
        </h2>
        <div className="grid sm:grid-cols-1 md:grid-cols-2 gap-4">
          <div>
            <p className="text-sm font-medium text-textSecondary">
              Network Active
            </p>
            <span
              className={`inline-block mt-1 px-3 py-1 text-sm font-medium rounded-full ${
                network.networkactive
                  ? 'bg-green-600 text-textPrimary'
                  : 'bg-red-600 text-textPrimary'
              }`}
            >
              {network.networkactive ? 'Active' : 'Inactive'}
            </span>
          </div>
          <div>
            <p className="text-sm font-medium text-textSecondary">Version</p>
            <p className="font-mono text-textPrimary mt-1">
              {network.subversion}
            </p>
          </div>
          <div>
            <p className="text-sm font-medium text-textSecondary">
              Protocol Version
            </p>
            <p className="font-mono text-textPrimary mt-1">
              {network.protocolversion}
            </p>
          </div>
          <div>
            <p className="text-sm font-medium text-textSecondary">Relay Fee</p>
            <p className="font-mono text-textPrimary mt-1">
              {network.relayfee} BTC
            </p>
          </div>
        </div>
      </div>
    </div>
  );
}
