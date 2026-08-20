import React, { useState } from 'react';
import TransactionDialog from './TransactionDialog';
import { shortenAddress } from './Utils';
import colors from '../../theme/colors';
import { TransactionTableProps } from './Types';

const TXID_REGEX = /^[a-fA-F0-9]{64}$/;

const STAGE_BADGE: Record<string, { label: string; color: string }> = {
  unknown: { label: 'Unknown', color: '#6b7280' },
  mempool: { label: 'Mempool', color: '#d97706' },
  staged: { label: 'Staged', color: '#3b82f6' },
  committed: { label: 'Committed', color: '#8b5cf6' },
  mined: { label: 'Mined', color: '#10b981' },
  confirmed: { label: 'Confirmed', color: '#22c55e' },
};

function StageBadge({ stage }: { stage?: string }) {
  const s = stage
    ? (STAGE_BADGE[stage] ?? STAGE_BADGE.unknown)
    : STAGE_BADGE.unknown;
  return (
    <span
      className="inline-block px-2 py-0.5 rounded-full text-xs font-medium"
      style={{
        backgroundColor: `${s.color}22`,
        color: s.color,
        border: `1px solid ${s.color}55`,
      }}
    >
      {s.label}
    </span>
  );
}

const TransactionTable: React.FC<TransactionTableProps> = ({
  transactions,
}) => {
  const [selectedTx, setSelectedTx] = useState<string | null>(null);
  const [lookupInput, setLookupInput] = useState('');
  const [lookupError, setLookupError] = useState<string | null>(null);
  const [stageFilter, setStageFilter] = useState<string>('all');

  const handleLookup = () => {
    const txid = lookupInput.trim();
    if (!TXID_REGEX.test(txid)) {
      setLookupError('Enter a valid 64-character hex txid');
      return;
    }
    setLookupError(null);
    setSelectedTx(txid);
  };

  const visibleTransactions =
    stageFilter === 'all'
      ? transactions
      : transactions.filter((tx: any) => tx.stage === stageFilter);
  const stageOptions = ['all', ...Object.keys(STAGE_BADGE)];

  return (
    <div
      className="rounded-2xl border border-white/10 bg-[#1e1e1e] shadow-md p-4"
      style={{ borderColor: colors.cardAccentSecondary }}
    >
      <div className="mb-3 text-gray-400">Latest Transactions</div>

      {/* Manual txid lookup + stage filter */}
      <div className="flex gap-2 mb-3">
        <select
          value={stageFilter}
          onChange={(e) => setStageFilter(e.target.value)}
          className="bg-[#2a2a2a] text-white text-xs rounded px-2 py-2 border border-white/10 focus:outline-none focus:border-white/30"
        >
          {stageOptions.map((s) => (
            <option key={s} value={s}>
              {s === 'all' ? 'All stages' : (STAGE_BADGE[s]?.label ?? s)}
            </option>
          ))}
        </select>
        <input
          type="text"
          placeholder="Look up txid (64-char hex)…"
          value={lookupInput}
          onChange={(e) => {
            setLookupInput(e.target.value);
            setLookupError(null);
          }}
          onKeyDown={(e) => e.key === 'Enter' && handleLookup()}
          className="flex-1 bg-[#2a2a2a] text-white text-xs rounded px-3 py-2 border border-white/10 focus:outline-none focus:border-white/30 font-mono"
          spellCheck={false}
        />
        <button
          onClick={handleLookup}
          className="px-3 py-2 text-xs rounded font-medium whitespace-nowrap"
          style={{ backgroundColor: colors.primary, color: '#fff' }}
        >
          Look Up
        </button>
      </div>
      {lookupError && (
        <p className="text-red-400 text-xs mb-2">{lookupError}</p>
      )}
      <div
        className="overflow-auto rounded-md scrollbar-thin"
        style={{
          scrollbarColor: `${colors.primary} ${colors.paper}`,
          backgroundColor: colors.paper,
        }}
      >
        <table className="w-full">
          {visibleTransactions.length === 0 ? null : (
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
                  STATUS
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
            {visibleTransactions.length === 0 ? (
              <tr>
                <td
                  colSpan={5}
                  className="p-4 text-center text-sm text-gray-400"
                >
                  {transactions.length === 0
                    ? 'No transactions found'
                    : `No ${stageFilter} transactions`}
                </td>
              </tr>
            ) : (
              visibleTransactions.map((tx) => (
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
                  <td className="p-4">
                    <StageBadge stage={tx.stage} />
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
