import { RecentBlocksTableProps } from './Types';
import colors from '../../theme/colors';
import { useState } from 'react';
import BlockInfoDialog from './BlockDialog';

function formatUnixTimestamp(timestamp: number): string {
  const date = new Date(timestamp * 1000);
  return date.toISOString().replace('T', ' ').slice(0, 19);
}

const RecentBlocksTable: React.FC<RecentBlocksTableProps> = ({
  maxHeight = 400,
  blocks,
}) => {
  const truncateHash = (hash: string) => {
    return hash.substring(0, 10) + '...' + hash.substring(hash.length - 10);
  };
  const [selectedBlock, setSelectedBlock] = useState<string | null>(null);

  return (
    <div
      className="rounded-2xl border border-white/10 bg-[#1e1e1e] shadow-md p-4"
      style={{ borderColor: colors.cardAccentSecondary }}
    >
      <div className="mb-2 text-sm text-gray-400">
        Latest blocks found by the pool
      </div>
      <div
        className="overflow-auto rounded-md scrollbar-thin"
        style={{
          maxHeight: `${maxHeight}px`,
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
                Height
              </th>
              <th
                className="text-left p-4 font-semibold text-sm"
                style={{ color: colors.textPrimary }}
              >
                ID
              </th>
              <th
                className="text-left p-4 font-semibold text-sm"
                style={{ color: colors.textPrimary }}
              >
                Time
              </th>
            </tr>
          </thead>
          <tbody>
            {blocks.map((block, index) => (
              <tr
                key={index}
                className="hover:bg-white/5 transition-colors duration-150"
                onClick={() => setSelectedBlock(block.id)}
              >
                <td
                  className="p-4 text-sm"
                  style={{ color: colors.textPrimary }}
                >
                  {block.height}
                </td>
                <td className="p-4 text-sm" style={{ color: colors.accent }}>
                  {truncateHash(block.id)}
                </td>
                <td
                  className="p-4 text-sm"
                  style={{ color: colors.textSecondary }}
                >
                  {formatUnixTimestamp(block.timestamp)}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
        {selectedBlock && (
          <BlockInfoDialog
            hash={selectedBlock}
            onClose={() => setSelectedBlock(null)}
          />
        )}
      </div>
    </div>
  );
};

export default RecentBlocksTable;
