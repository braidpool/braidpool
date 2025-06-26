import colors from '../../theme/colors';
import { RBFTransactionRowProps } from './Types';
import { shortenAddress } from './Utils';

export const RBFTransactionRow: React.FC<RBFTransactionRowProps> = ({
  isReplacement,
  tx,
  depth = 0,
  onSelect,
  expandedTxs,
  toggleExpanded,
}) => {
  const txData = tx.tx;
  const indent = depth * 20;
  const isExpanded = expandedTxs.has(txData.txid);
  const hasReplacements = tx.replaces && tx.replaces.length > 0;

  return (
    <>
      <tr className="hover:bg-white/5 transition-colors duration-150">
        <td className="px-4 py-2" style={{ paddingLeft: indent + 16 }}>
          <div className="flex items-center gap-2">
            {hasReplacements && (
              <button
                className={`text-xs text-gray-400 hover:text-white transition transform ${isExpanded ? 'rotate-90' : 'rotate-0'}`}
                onClick={() => toggleExpanded(txData.txid)}
              >
                ▶
              </button>
            )}
            <div
              className="relative group inline-block cursor-pointer hover:underline"
              style={{ color: colors.accent }}
              onClick={() => !isReplacement && onSelect(txData.txid)}
            >
              {shortenAddress(txData.txid)}{' '}
              {isReplacement && (
                <span className="text-xs text-gray-500">(Replaced)</span>
              )}
              <div
                className="absolute z-50 opacity-0 group-hover:opacity-100 transition-opacity duration-200 
                                bg-gray-800 text-white p-2 rounded shadow-lg text-xs whitespace-nowrap
                                left-full top-1/2 -translate-y-1/2 ml-2"
              >
                {txData.txid}
              </div>
            </div>
          </div>
        </td>
        <td className="px-4 py-2">{(txData.fee / 1e8).toFixed(8)} BTC</td>
        <td className="px-4 py-2">{(txData.value / 1e8).toFixed(8)} BTC</td>
        <td className="px-4 py-2">{txData.rate.toFixed(2)} sat/vB</td>
      </tr>

      {isExpanded &&
        tx.replaces &&
        tx.replaces.map((replacedTx, idx) => (
          <RBFTransactionRow
            isReplacement={true}
            key={replacedTx.tx.txid + idx}
            tx={replacedTx}
            depth={depth + 1}
            onSelect={onSelect}
            expandedTxs={expandedTxs}
            toggleExpanded={toggleExpanded}
          />
        ))}
    </>
  );
};
