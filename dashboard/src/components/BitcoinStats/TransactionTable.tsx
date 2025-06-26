import React, { useState } from 'react';
import TransactionDialog from './TransactionDialog';
import { shortenAddress } from './Utils';
import colors from '../../theme/colors';
import { TransactionTableProps } from './Types';

const TransactionTable: React.FC<TransactionTableProps> = ({
  transactions,
}) => {
  const [selectedTx, setSelectedTx] = useState<string | null>(null);
  return (
    <div
      className="rounded-2xl border border-white/10 bg-[#1e1e1e] shadow-md p-4"
      style={{ borderColor: colors.cardAccentSecondary }}
    >
      <div className="mb-2  text-gray-400">Latest Transactions</div>
      <div
        className="overflow-auto rounded-md scrollbar-thin"
        style={{
          scrollbarColor: `${colors.primary} ${colors.paper}`,
          backgroundColor: colors.paper,
        }}
      >
        <table className="w-full">
          {transactions.length === 0 ? null : (
            <thead className="sticky top-0 z-10">
              <tr style={{ backgroundColor: colors.paper }}>
                <th
                  className="text-left p-4 font-semibold "
                  style={{ color: colors.textPrimary }}
                >
                  TXID
                </th>
                <th
                  className="text-left p-4 font-semibold "
                  style={{ color: colors.textPrimary }}
                >
                  FEE
                </th>
                <th
                  className="text-left p-4 font-semibold "
                  style={{ color: colors.textPrimary }}
                >
                  SIZE
                </th>
                <th
                  className="text-left p-4 font-semibold "
                  style={{ color: colors.textPrimary }}
                >
                  VALUE
                </th>
              </tr>
            </thead>
          )}
          <tbody>
            {transactions.length === 0 ? (
              <tr>
                <td
                  colSpan={4}
                  className="p-4 text-center text-sm text-gray-400"
                >
                  No transactions found
                </td>
              </tr>
            ) : (
              transactions.map((tx) => (
                <tr
                  key={tx.txid}
                  className={`transition-colors duration-150 ${
                    selectedTx === tx.txid ? 'bg-white/10' : 'hover:bg-white/10'
                  }`}
                  onClick={() => setSelectedTx(tx.txid)}
                >
                  <td className="p-4">
                    <div className="relative group inline-block">
                      <span
                        className="cursor-pointer hover:underline"
                        style={{ color: colors.accent }}
                      >
                        {shortenAddress(tx.txid)}
                      </span>
                      <div
                        className="absolute z-50 opacity-0 group-hover:opacity-100 transition-opacity duration-200 
                  bg-gray-800 text-white p-2 rounded shadow-lg text-xs whitespace-nowrap
                  left-full top-1/2 -translate-y-1/2 ml-2"
                      >
                        {tx.txid}
                      </div>
                    </div>
                  </td>
                  <td className="p-4" style={{ color: colors.textPrimary }}>
                    {tx.fee / 100000000} BTC
                  </td>
                  <td className="p-4" style={{ color: colors.textPrimary }}>
                    {tx.vsize} vB
                  </td>
                  <td className="p-4" style={{ color: colors.textPrimary }}>
                    {tx.value / 100000000} BTC
                  </td>
                </tr>
              ))
            )}
          </tbody>
        </table>

        {selectedTx && (
          <TransactionDialog
            txid={selectedTx}
            onClose={() => setSelectedTx(null)}
          />
        )}
      </div>
    </div>
  );
};

export default TransactionTable;
