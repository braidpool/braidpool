import React, { useState } from 'react';
import colors from '../../theme/colors';
import { TransactionTableProps } from './Types';
import RBFTransactionDialog from './RBFTransactionDialog';
import { RBFTransactionRow } from './RBFTransactionRow';

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
          {transactions.length === 0 ? null : (
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
              </tr>
            </thead>
          )}
          <tbody>
            {transactions.length === 0 ? (
              <tr>
                <td
                  colSpan={5}
                  className="p-4 text-center text-sm text-gray-400"
                >
                  No RBF transactions found
                </td>
              </tr>
            ) : (
              transactions.map((tx, idx) => (
                <RBFTransactionRow
                  key={tx.tx.txid + idx}
                  tx={tx}
                  onSelect={setSelectedTx}
                  expandedTxs={expandedTxs}
                  toggleExpanded={toggleExpanded}
                />
              ))
            )}
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
