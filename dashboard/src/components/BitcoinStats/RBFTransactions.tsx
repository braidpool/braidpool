import React, { useState } from 'react';
import { shortenAddress } from './Utils';
import colors from '../../theme/colors';
import { TransactionTableProps, RBFTransactionRowProps } from './Types';
import RBFTransactionDialog from './RBFTransactionDialog';

const RBFTransactionRow: React.FC<RBFTransactionRowProps> = ({
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
        <td className="px-4 py-2">
          {txData.rbf ? (txData.fullRbf ? 'Full RBF' : 'RBF') : 'No'}
        </td>
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

const RBFTransactionTable: React.FC<TransactionTableProps> = ({
  transactions,
}) => {
  const [selectedTx, setSelectedTx] = useState<string | null>(null);
  const [expandedTxs, setExpandedTxs] = useState<Set<string>>(new Set());

  const toggleExpanded = (txid: string) => {
    setExpandedTxs((prev) => {
      const newSet = new Set(prev);
      if (newSet.has(txid)) {
        newSet.delete(txid);
      } else {
        newSet.add(txid);
      }
      return newSet;
    });
  };

  return (
    <div
      className="rounded-2xl border mt-10 border-white/10 bg-[#1e1e1e] shadow-md p-4"
      style={{ borderColor: colors.cardAccentSecondary }}
    >
      <div className="mb-2  text-gray-400">Latest RBF Transactions</div>
      <div
        className="overflow-auto rounded-md scrollbar-thin"
        style={{
          maxHeight: '400px',
          overflowY: 'auto',
          scrollbarColor: `${colors.primary} ${colors.paper}`,
          backgroundColor: colors.paper,
        }}
      >
        <table className="w-full ">
          <thead
            className="sticky top-0 z-10"
            style={{ backgroundColor: colors.paper }}
          >
            <tr>
              <th
                className="text-left px-4 py-2"
                style={{ color: colors.textPrimary }}
              >
                TXID
              </th>
              <th
                className="text-left px-4 py-2"
                style={{ color: colors.textPrimary }}
              >
                FEE
              </th>
              <th
                className="text-left px-4 py-2"
                style={{ color: colors.textPrimary }}
              >
                VALUE
              </th>
              <th
                className="text-left px-4 py-2"
                style={{ color: colors.textPrimary }}
              >
                RATE
              </th>
              <th
                className="text-left px-4 py-2"
                style={{ color: colors.textPrimary }}
              >
                RBF
              </th>
            </tr>
          </thead>
          <tbody>
            {transactions.map((tx, idx) => (
              <RBFTransactionRow
                key={tx.tx.txid + idx}
                tx={tx}
                onSelect={setSelectedTx}
                expandedTxs={expandedTxs}
                toggleExpanded={toggleExpanded}
              />
            ))}
          </tbody>
        </table>
      </div>

      {selectedTx && (
        <RBFTransactionDialog
          txid={selectedTx}
          onClose={() => setSelectedTx(null)}
        />
      )}
    </div>
  );
};

export default RBFTransactionTable;
