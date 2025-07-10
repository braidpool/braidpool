import { useState, useEffect } from 'react';
import { getTxInfo, useCopyToClipboard } from './Utils';
import { CopyIcon } from 'lucide-react';

const TransactionDialog = ({
  txid,
  onClose,
}: {
  txid: string;
  onClose: () => void;
}) => {
  const [txInfo, setTxInfo] = useState<any>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [copied, copyToClipboard] = useCopyToClipboard();

  useEffect(() => {
    setLoading(true);
    setError(null);
    const fetchData = async () => {
      try {
        const data = await getTxInfo(txid);
        setTxInfo(data);
      } catch (err) {
        setError('Failed to load transaction details');
        console.error(err);
      } finally {
        setLoading(false);
      }
    };

    fetchData();
  }, [txid]);

  return (
    <>
      {/* Clickable overlay that closes the dialog */}
      <div className="fixed inset-0 z-40" onClick={onClose} />

      {/* Transaction details sidebar */}
      <div className="fixed right-0 top-14 z-50 h-[calc(100%-3.5rem)] w-full max-w-md sm:w-96 bg-[#1e1e1e] overflow-y-auto shadow-2xl text-white border border-gray-700">
        <div className="sticky top-0 border-white bg-[#1e1e1e] p-4 flex justify-between items-center">
          <h2 className="text-lg font-bold">Transaction Details</h2>
          <button
            onClick={onClose}
            className="text-gray-400 hover:text-white p-1 rounded-full hover:border-white/10 bg-[#1e1e1e]"
            aria-label="Close dialog"
          >
            ✕
          </button>
        </div>

        <div className="p-4 space-y-4">
          {loading && (
            <div className="text-center py-8">Loading transaction data...</div>
          )}
          {error && (
            <div className="text-red-500 py-8 text-center">{error}</div>
          )}

          {txInfo && (
            <>
              <div className="space-y-3">
                <div>
                  <h3 className="text-sm font-medium text-gray-400">
                    Transaction ID
                  </h3>
                  <p className="text-sm break-all mt-1">
                    {txInfo.txid}
                    <button
                      onClick={() => copyToClipboard(txInfo.txid)}
                      className="text-gray-400 hover:text-white ml-2"
                      title="Copy to clipboard"
                      aria-label="Copy transaction ID"
                    >
                      <CopyIcon className="inline w-4 h-4" />
                    </button>
                    {copied && (
                      <span className="ml-2 text-green-400 text-xs">
                        Copied!
                      </span>
                    )}
                  </p>
                </div>

                <div className="grid grid-cols-2 gap-4">
                  <div>
                    <h3 className="text-sm font-medium text-gray-400">
                      Status
                    </h3>
                    <p className="text-sm mt-1">
                      {txInfo.status.confirmed ? 'Confirmed' : 'Unconfirmed'}
                    </p>
                  </div>
                  <div>
                    <h3 className="text-sm font-medium text-gray-400">Fee</h3>
                    <p className="text-sm mt-1">{txInfo.fee / 100000000} BTC</p>
                  </div>
                  <div>
                    <h3 className="text-sm font-medium text-gray-400">Size</h3>
                    <p className="text-sm mt-1">{txInfo.size} bytes</p>
                  </div>
                  <div>
                    <h3 className="text-sm font-medium text-gray-400">
                      Weight
                    </h3>
                    <p className="text-sm mt-1">{txInfo.weight} WU</p>
                  </div>
                  <div>
                    <h3 className="text-sm font-medium text-gray-400">
                      Version
                    </h3>
                    <p className="text-sm mt-1">{txInfo.version}</p>
                  </div>
                  <div>
                    <h3 className="text-sm font-medium text-gray-400">
                      Locktime
                    </h3>
                    <p className="text-sm mt-1">{txInfo.locktime}</p>
                  </div>
                </div>
              </div>

              <div className="pt-6 border-t border-gray-700">
                <h3 className="font-medium text-gray-400 mb-2">
                  Inputs ({txInfo.vin.length})
                </h3>
                <div className="space-y-3">
                  {txInfo.vin.map((input: any, index: number) => (
                    <div key={index} className="bg-[#2a2a2a] rounded p-3">
                      <p className="text-xs break-all">
                        <span className="font-medium">From:</span>{' '}
                        {input.prevout?.scriptpubkey_address || 'Coinbase'}
                      </p>
                      <p className="text-xs mt-1">
                        <span className="font-medium">Amount:</span>{' '}
                        {input.prevout?.value
                          ? `${input.prevout.value / 100000000} BTC`
                          : 'N/A'}
                      </p>
                    </div>
                  ))}
                </div>
              </div>

              <div className="pt-6 border-t border-gray-700">
                <h3 className="font-medium text-gray-400 mb-2">
                  Outputs ({txInfo.vout.length})
                </h3>
                <div className="space-y-3">
                  {txInfo.vout.map((output: any, index: number) => (
                    <div key={index} className="bg-[#2a2a2a] rounded p-3">
                      <p className="text-xs break-all">
                        <span className="font-medium">To:</span>{' '}
                        {output.scriptpubkey_address}
                      </p>
                      <p className="text-xs mt-1">
                        <span className="font-medium">Amount:</span>{' '}
                        {output.value / 100000000} BTC
                      </p>
                    </div>
                  ))}
                </div>
              </div>
            </>
          )}
        </div>
      </div>
    </>
  );
};

export default TransactionDialog;
