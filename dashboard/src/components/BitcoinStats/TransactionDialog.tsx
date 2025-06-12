import { useState, useEffect } from 'react';
import { getTxInfo } from './Utils';
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
  const [copied, setCopied] = useState(false);

  const handleCopy = () => {
    navigator.clipboard.writeText(txInfo.txid);
    setCopied(true);
    setTimeout(() => setCopied(false), 1500);
  };

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
      <div className="pt-14 fixed right-0 top-0 z-50 h-full w-96 bg-gray-800 overflow-y-auto shadow-xl">
        <div className="sticky top-0 bg-gray-800 p-4 border-b border-gray-700 flex justify-between items-center">
          <h2 className="text-lg font-bold">Transaction Details</h2>
          <button
            onClick={onClose}
            className="text-gray-400 hover:text-white p-1 rounded-full hover:bg-gray-700"
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
                      onClick={handleCopy}
                      className="text-gray-400 hover:text-white ml-2"
                      title="Copy to clipboard"
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

              <div className="pt-4">
                <h3 className="font-medium text-gray-400 mb-2">
                  Inputs ({txInfo.vin.length})
                </h3>
                <div className="space-y-3">
                  {txInfo.vin.map((input: any, index: number) => (
                    <div key={index} className="bg-gray-700 rounded p-3">
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

              <div className="pt-4">
                <h3 className="font-medium text-gray-400 mb-2">
                  Outputs ({txInfo.vout.length})
                </h3>
                <div className="space-y-3">
                  {txInfo.vout.map((output: any, index: number) => (
                    <div key={index} className="bg-gray-700 rounded p-3">
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
