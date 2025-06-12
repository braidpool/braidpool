import React from 'react';
import TransactionDialog from './TransactionDialog';
import { shortenAddress } from './Utils';
import colors from '../../theme/colors';
import { TransactionTableProps } from './Types';

const TransactionTable: React.FC<TransactionTableProps> = ({
  transactions,
  selectedTx,
  setSelectedTx,
}) => {
  return (
    <div
      className="rounded-2xl border border-white/10 bg-[#1e1e1e] shadow-md p-4"
      style={{ borderColor: colors.cardAccentSecondary }}
    >
      <div className="mb-2 text-sm text-gray-400">Latest Transactions</div>
      <div
        className="overflow-auto rounded-md scrollbar-thin"
        style={{
          scrollbarColor: `${colors.primary} ${colors.paper}`,
          backgroundColor: colors.paper,
        }}
      >
        <table className="w-full">
          <thead className="sticky top-0 z-10">
            <tr style={{ backgroundColor: colors.paper }}>
              <th
                className="text-left p-4 font-semibold text-sm"
                style={{ color: colors.textPrimary }}
              >
                TXID
              </th>
              <th
                className="text-left p-4 font-semibold text-sm"
                style={{ color: colors.textPrimary }}
              >
                FEE
              </th>
              <th
                className="text-left p-4 font-semibold text-sm"
                style={{ color: colors.textPrimary }}
              >
                SIZE
              </th>
              <th
                className="text-left p-4 font-semibold text-sm"
                style={{ color: colors.textPrimary }}
              >
                VALUE
              </th>
            </tr>
          </thead>
          <tbody>
            {transactions.map((tx, txid) => (
              <tr
                key={txid}
                className="hover:bg-white/5 transition-colors duration-150"
                onClick={() => setSelectedTx(tx.txid)}
              >
                <td className="px-4 py-2">
                  <div className="relative group inline-block">
                    <span className="cursor-pointer hover:underline">
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
                <td className="px-4 py-2">{tx.fee / 100000000} BTC</td>
                <td className="px-4 py-2">{tx.vsize} vB</td>
                <td className="px-4 py-2">{tx.value / 100000000} BTC</td>
              </tr>
            ))}
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
