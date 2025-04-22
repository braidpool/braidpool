import React from 'react';
import {
  Table,
  TableBody,
  TableCell,
  TableContainer,
  TableHead,
  TableRow,
  Box,
  Typography,
} from '@mui/material';
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
  // Helper function to truncate hash
  const truncateHash = (hash: string) => {
    return hash.substring(0, 10) + '...' + hash.substring(hash.length - 10);
  };

  return (
    <Card
      title="Recent Blocks"
      subtitle="Latest blocks found by the pool"
      accentColor={colors.cardAccentSecondary}
    >
      <TableContainer
        sx={{
          maxHeight: maxHeight,
          '&::-webkit-scrollbar': {
            width: '8px',
          },
          '&::-webkit-scrollbar-track': {
            background: colors.paper,
          },
          '&::-webkit-scrollbar-thumb': {
            background: colors.primary,
            borderRadius: '4px',
          },
        }}
      >
        <Table size="medium" stickyHeader>
          <TableHead>
            <TableRow>
              <TableCell
                sx={{
                  backgroundColor: colors.paper,
                  color: colors.textPrimary,
                  fontWeight: 'bold',
                }}
              >
                Height
              </TableCell>
              <TableCell
                sx={{
                  backgroundColor: colors.paper,
                  color: colors.textPrimary,
                  fontWeight: 'bold',
                }}
              >
                Hash
              </TableCell>
              <TableCell
                sx={{
                  backgroundColor: colors.paper,
                  color: colors.textPrimary,
                  fontWeight: 'bold',
                }}
              >
                Time
              </TableCell>
            </TableRow>
          </TableHead>
          <TableBody>
            {recentBlocks.map((block, index) => (
              <TableRow
                key={index}
                sx={{
                  '&:hover': {
                    backgroundColor: 'rgba(255, 255, 255, 0.05)',
                  },
                }}
              >
                <TableCell sx={{ color: colors.textPrimary }}>
                  {block.height}
                </TableCell>
                <TableCell sx={{ color: colors.accent }}>
                  {truncateHash(block.hash)}
                </TableCell>
                <TableCell sx={{ color: colors.textSecondary }}>
                  {block.time}
                </TableCell>
              </TableRow>
            ))}
          </TableBody>
        </Table>
      </TableContainer>
    </Card>
  );
};

export default RecentBlocksTable;
