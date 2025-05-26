import React from 'react';
import Card from '../common/Card';
import colors from '../../theme/colors';

// Mock data for recent blocks
const recentBlocks = [
  {
    height: 837192,
    hash: '000000000000000000030f31e862f407bb97d0d299e6ae92b428b540f8d26237',
    time: '4 hrs ago',
  },
  {
    height: 837192,
    hash: '000000000000000000023a97e8c10a8ba61827f37b019871bf3aab48015d3273',
    time: '5 hrs ago',
  },
  {
    height: 837192,
    hash: '0000000000000000000b98c4d0ff2b7d48ab5aeadcfb94c53fef7b9e18982f34',
    time: '6 hrs ago',
  },
  {
    height: 837192,
    hash: '00000000000000000007f3e72173d22dd9fbd000b7acb328c5559346b5f6af89',
    time: '7 hrs ago',
  },
];

interface RecentBlocksTableProps {
  maxHeight?: number;
}

const RecentBlocksTable: React.FC<RecentBlocksTableProps> = ({
  maxHeight = 400,
}) => {
  const truncateHash = (hash: string) => {
    return hash.substring(0, 10) + '...' + hash.substring(hash.length - 10);
  };

  return (
    <Card
      subtitle="Latest blocks found by the pool"
      accentColor={colors.cardAccentSecondary}
    >
      <div
        className="overflow-auto"
        style={{
          maxHeight: `${maxHeight}px`,
          scrollbarWidth: 'thin',
          scrollbarColor: `${colors.primary} ${colors.paper}`,
        }}
      >
        <table className="w-full">
          <thead className="sticky top-0">
            <tr style={{ backgroundColor: colors.paper }}>
              <th
                className="text-left p-4 font-bold"
                style={{ color: colors.textPrimary }}
              >
                Height
              </th>
              <th
                className="text-left p-4 font-bold"
                style={{ color: colors.textPrimary }}
              >
                Hash
              </th>
              <th
                className="text-left p-4 font-bold"
                style={{ color: colors.textPrimary }}
              >
                Time
              </th>
            </tr>
          </thead>
          <tbody>
            {recentBlocks.map((block, index) => (
              <tr key={index} className="hover:bg-white/5 transition-colors">
                <td className="p-4" style={{ color: colors.textPrimary }}>
                  {block.height}
                </td>
                <td className="p-4" style={{ color: colors.accent }}>
                  {truncateHash(block.hash)}
                </td>
                <td className="p-4" style={{ color: colors.textSecondary }}>
                  {block.time}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </Card>
  );
};

export default RecentBlocksTable;
