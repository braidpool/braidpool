import { useState, useEffect } from 'react';
import { getBlockInfo } from './Utils';
import { CopyIcon } from 'lucide-react';

const BlockInfoDialog = ({
  hash,
  onClose,
}: {
  hash: string;
  onClose: () => void;
}) => {
  const [blockInfo, setBlockInfo] = useState<any>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [copied, setCopied] = useState(false);

  const handleCopy = () => {
    if (blockInfo?.id) {
      navigator.clipboard.writeText(blockInfo.id);
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    }
  };

  useEffect(() => {
    setLoading(true);
    setError(null);

    const fetchData = async () => {
      try {
        const data = await getBlockInfo(hash);
        setBlockInfo(data);
      } catch (err) {
        setError('Failed to load block details');
        console.error(err);
      } finally {
        setLoading(false);
      }
    };

    fetchData();
  }, [hash]);

  const formatTimestamp = (ts: number) => {
    const d = new Date(ts * 1000);
    return d.toLocaleString();
  };

  return (
    <>
      <div className="fixed inset-0 z-40" onClick={onClose} />

      {/* Block details sidebar */}
      <div className="pt-14 fixed right-0 top-0 z-50 h-full w-96 bg-gray-800 overflow-y-auto shadow-xl text-white">
        <div className="sticky top-0 bg-gray-800 p-4 border-b border-gray-700 flex justify-between items-center">
          <h2 className="text-lg font-bold">Block Details</h2>
          <button
            onClick={onClose}
            className="text-gray-400 hover:text-white p-1 rounded-full hover:bg-gray-700"
            aria-label="Close dialog"
          >
            ✕
          </button>
        </div>

        <div className="p-4 space-y-4">
          {loading && (
            <div className="text-center py-8">Loading block data...</div>
          )}
          {error && (
            <div className="text-red-500 py-8 text-center">{error}</div>
          )}

          {blockInfo && (
            <>
              <div>
                <h3 className="text-sm font-medium text-gray-400">
                  Block ID (Hash)
                </h3>
                <p className="text-sm break-all mt-1">
                  {blockInfo.id}
                  <button
                    onClick={handleCopy}
                    className="text-gray-400 hover:text-white ml-2"
                    title="Copy to clipboard"
                    aria-label="Copy block hash"
                  >
                    <CopyIcon className="inline w-4 h-4" />
                  </button>
                  {copied && (
                    <span className="ml-2 text-green-400 text-xs">Copied!</span>
                  )}
                </p>
              </div>

              <div className="grid grid-cols-2 gap-4">
                <div>
                  <h3 className="text-sm font-medium text-gray-400">Height</h3>
                  <p className="text-sm mt-1">{blockInfo.height}</p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">
                    Timestamp
                  </h3>
                  <p className="text-sm mt-1">
                    {formatTimestamp(blockInfo.timestamp)}
                  </p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">Version</h3>
                  <p className="text-sm mt-1">{blockInfo.version}</p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">Bits</h3>
                  <p className="text-sm mt-1">{blockInfo.bits}</p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">Nonce</h3>
                  <p className="text-sm mt-1">{blockInfo.nonce}</p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">
                    Difficulty
                  </h3>
                  <p className="text-sm mt-1">
                    {blockInfo.difficulty.toLocaleString()}
                  </p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">
                    Merkle Root
                  </h3>
                  <p className="text-sm break-all mt-1">
                    {blockInfo.merkle_root}
                  </p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">
                    Transaction Count
                  </h3>
                  <p className="text-sm mt-1">{blockInfo.tx_count}</p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">Size</h3>
                  <p className="text-sm mt-1">
                    {blockInfo.size.toLocaleString()} bytes
                  </p>
                </div>
                <div>
                  <h3 className="text-sm font-medium text-gray-400">Weight</h3>
                  <p className="text-sm mt-1">
                    {blockInfo.weight.toLocaleString()} WU
                  </p>
                </div>
                <div className="col-span-2">
                  <h3 className="text-sm font-medium text-gray-400">
                    Previous Block Hash
                  </h3>
                  <p className="text-sm break-all mt-1">
                    {blockInfo.previousblockhash || 'N/A'}
                  </p>
                </div>
              </div>

              {blockInfo.extras && (
                <div className="pt-6 border-t border-gray-700">
                  <h3 className="font-medium text-gray-400 mb-2">Extras</h3>
                  <div className="text-sm space-y-2">
                    <p>
                      <strong>Reward:</strong>{' '}
                      {(blockInfo.extras.reward / 100000000).toFixed(8)} BTC
                    </p>
                    <p>
                      <strong>Total Fees:</strong>{' '}
                      {(blockInfo.extras.totalFees / 100000000).toFixed(8)} BTC
                    </p>
                    <p>
                      <strong>Pool:</strong>{' '}
                      {blockInfo.extras.pool?.name || 'N/A'}
                    </p>
                    <p>
                      <strong>Match Rate:</strong>{' '}
                      {blockInfo.extras.matchRate || 'N/A'}%
                    </p>
                    <p>
                      <strong>Median Fee:</strong>{' '}
                      {blockInfo.extras.medianFee || 'N/A'} sats
                    </p>
                  </div>
                </div>
              )}
            </>
          )}
        </div>
      </div>
    </>
  );
};

export default BlockInfoDialog;
