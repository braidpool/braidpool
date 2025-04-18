import React from 'react';
import {
  Box,
  Card,
  Typography,
  CircularProgress,
  Tooltip,
  useTheme,
} from '@mui/material';
import TrendingUpIcon from '@mui/icons-material/TrendingUp';
import TrendingDownIcon from '@mui/icons-material/TrendingDown';
import InfoOutlinedIcon from '@mui/icons-material/InfoOutlined';

interface KPICardProps {
  title: string;
  value: string | number;
  unit?: string;
  change?: number;
  subtitle?: string;
  loading?: boolean;
  info?: string;
  icon?: React.ReactNode;
}

const KPICard: React.FC<KPICardProps> = ({
  title,
  value,
  unit,
  change,
  subtitle,
  loading = false,
  info,
  icon,
}) => {
  const theme = useTheme();

  const renderTrend = () => {
    if (change === undefined) return null;

    const isPositive = change >= 0;
    const color = isPositive
      ? theme.palette.success.main
      : theme.palette.error.main;
    const Icon = isPositive ? TrendingUpIcon : TrendingDownIcon;

    return (
      <Box sx={{ display: 'flex', alignItems: 'center', color, mt: 0.5 }}>
        <Icon fontSize='small' sx={{ mr: 0.5 }} />
        <Typography variant='body2' component='span' sx={{ color }}>
          {Math.abs(change)}% {isPositive ? 'increase' : 'decrease'}
        </Typography>
      </Box>
    );
  };

  return (
    <Card
      sx={{
        p: 2,
        display: 'flex',
        flexDirection: 'column',
        height: '100%',
        minHeight: 90,
        boxShadow: '0 1px 3px rgba(0,0,0,0.05)',
        borderRadius: 1,
        border: '1px solid rgba(0,0,0,0.05)',
        backgroundColor: '#fff',
      }}>
      {/* Subtitle first (if provided) - matches FOREMAN layout */}
      {subtitle && (
        <Typography
          variant='caption'
          color='text.secondary'
          sx={{
            fontSize: '0.7rem',
            textTransform: 'uppercase',
            textAlign: 'center',
            mb: 0.5,
          }}>
          {subtitle}
        </Typography>
      )}

      {/* Value section with large font */}
      <Box
        sx={{
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'flex-end',
          mb: 0.5,
        }}>
        {loading ? (
          <CircularProgress size={24} sx={{ my: 1 }} />
        ) : (
          <>
            <Typography
              variant='h5'
              component='div'
              fontWeight='bold'
              sx={{ textAlign: 'center' }}>
              {value}
            </Typography>
            {unit && (
              <Typography
                variant='body2'
                color='text.secondary'
                sx={{ ml: 0.5, mb: 0.2 }}>
                {unit}
              </Typography>
            )}
          </>
        )}
      </Box>

      {/* Title below the value - matches FOREMAN layout */}
      <Typography
        variant='subtitle2'
        color='text.secondary'
        sx={{
          textAlign: 'center',
          fontSize: '0.75rem',
          fontWeight: 'normal',
          color: '#666',
        }}>
        {title}
      </Typography>

      {/* Trend indicator at bottom */}
      <Box sx={{ display: 'flex', justifyContent: 'center', mt: 'auto' }}>
        {renderTrend()}
      </Box>

      {/* Info icon if needed */}
      {info && (
        <Tooltip title={info} arrow placement='top'>
          <InfoOutlinedIcon
            fontSize='small'
            sx={{
              position: 'absolute',
              top: 8,
              right: 8,
              color: 'text.secondary',
              cursor: 'help',
              opacity: 0.6,
            }}
          />
        </Tooltip>
      )}
    </Card>
  );
};

export default KPICard;
