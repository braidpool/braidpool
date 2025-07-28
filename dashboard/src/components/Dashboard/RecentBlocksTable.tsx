import { RecentBlocksTableProps } from './Types';
import colors from '../../theme/colors';
import { useState } from 'react';
import BlockInfoDialog from './BlockDialog';
import { formatUnixTimestamp } from './Utils';
import { shortenAddress } from '../BitcoinStats/Utils';

const RecentBlocksTable: React.FC<RecentBlocksTableProps> = ({
  maxHeight = 400,
  blocks,
}) => {
  const [selectedBlock, setSelectedBlock] = useState<string | null>(null);

  return (
    <div className="max-w-screen w-full overflow-x-hidden">
      <div
        className="rounded-2xl border border-white/10 bg-[#1e1e1e] shadow-md p-4"
        style={{ borderColor: colors.cardAccentSecondary }}
      >
        <div className="mb-2  text-gray-400">
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
                  className="text-left p-4 font-semibold "
                  style={{ color: colors.textPrimary }}
                >
                  Height
                </th>
                <th
                  className="text-left p-4 font-semibold "
                  style={{ color: colors.textPrimary }}
                >
                  ID
                </th>
                <th
                  className="text-left p-4 font-semibold "
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
                  className={`transition-colors duration-150 ${
                    selectedBlock === block.id
                      ? 'bg-white/10'
                      : 'hover:bg-white/10'
                  }`}
                  onClick={() => setSelectedBlock(block.id)}
                >
                  <td className="p-4" style={{ color: colors.textPrimary }}>
                    {block.height}
                  </td>
                  <td
                    className="p-4 relative group inline-block cursor-pointer hover:underline"
                    style={{ color: colors.accent }}
                  >
                    {shortenAddress(block.id)}
                  </td>
                  <td className="p-4 " style={{ color: colors.textSecondary }}>
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
    </div>
  );
};

export default RecentBlocksTable;
