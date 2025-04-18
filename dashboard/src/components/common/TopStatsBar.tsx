import React from 'react';
import { Box, Typography, Stack, Skeleton } from '@mui/material';
import colors from '../../theme/colors';

interface StatCardProps {
  title: string;
  value: string;
  icon?: React.ReactNode;
  loading?: boolean;
}

interface TopStatsBarProps {
  loading?: boolean;
}

const StatCard: React.FC<StatCardProps> = ({
  title,
  value,
  icon,
  loading = false,
}) => {
  return (
    <Box
      sx={{
        backgroundColor: colors.paper,
        borderRadius: 1,
        padding: 2,
        height: '100%',
        border: `1px solid ${colors.border}`,
        transition: 'transform 0.2s',
        '&:hover': {
          transform: 'translateY(-3px)',
          boxShadow: `0 8px 16px -8px ${colors.shadow}`,
        },
      }}>
      <Box sx={{ display: 'flex', alignItems: 'center', mb: 1 }}>
        {icon && <Box sx={{ mr: 1, color: colors.primary }}>{icon}</Box>}
        <Typography variant='subtitle2' color='textSecondary'>
          {title}
        </Typography>
      </Box>
      {loading ? (
        <Skeleton variant='text' width='80%' height={40} />
      ) : (
        <Typography
          variant='h4'
          sx={{
            fontWeight: 700,
            color: colors.textPrimary,
            overflow: 'hidden',
            textOverflow: 'ellipsis',
          }}>
          {value}
        </Typography>
      )}
    </Box>
  );
};

const TopStatsBar: React.FC<TopStatsBarProps> = ({ loading = false }) => {
  return (
    <Box sx={{ mb: 3 }}>
      <Stack
        direction={{ xs: 'column', sm: 'row' }}
        spacing={3}
        sx={{ width: '100%' }}>
        <Box sx={{ width: { xs: '100%', sm: '25%' } }}>
          <StatCard
            title='Shares Submitted'
            value='208,450'
            loading={loading}
          />
        </Box>
        <Box sx={{ width: { xs: '100%', sm: '25%' } }}>
          <StatCard title='Stale Shares' value='756' loading={loading} />
        </Box>
        <Box sx={{ width: { xs: '100%', sm: '25%' } }}>
          <StatCard title='Pool Hashrate' value='98.3 PH/s' loading={loading} />
        </Box>
        <Box sx={{ width: { xs: '100%', sm: '25%' } }}>
          <StatCard title='Recent Blocks Won' value='34' loading={loading} />
        </Box>
      </Stack>
    </Box>
  );
};

export default TopStatsBar;
