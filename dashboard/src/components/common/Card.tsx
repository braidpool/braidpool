import React from 'react';
import { Box, Paper, Typography } from '@mui/material';
import { CardProps } from './Types';

/**
 * A reusable card component with a standard styling pattern
 * used throughout the dashboard
 */
const Card: React.FC<CardProps> = ({
  title,
  subtitle,
  children,
  accentColor = '#1976d2',
  headerExtra,
}) => {
  return (
    <Paper
      elevation={0}
      sx={{
        p: 0,
        borderRadius: 1,
        border: '1px solid rgba(0,0,0,0.05)',
        boxShadow: '0 2px 4px rgba(0,0,0,0.03)',
        overflow: 'hidden',
        height: '100%',
        ...(accentColor && {
          position: 'relative',
          '&::after': {
            content: '""',
            position: 'absolute',
            top: 0,
            left: 0,
            width: '4px',
            height: '100%',
            backgroundColor: accentColor,
          },
        }),
      }}
    >
      {(title || subtitle || headerExtra) && (
        <Box
          sx={{
            px: 2,
            py: 1.5,
            borderBottom: '1px solid rgba(0,0,0,0.05)',
            display: 'flex',
            justifyContent: 'space-between',
            alignItems: 'center',
            bgcolor: 'rgba(0,0,0,0.01)',
          }}
        >
          <Box>
            {title && (
              <Typography
                variant="subtitle1"
                sx={{ fontWeight: 500, color: 'text.primary' }}
              >
                {title}
              </Typography>
            )}
            {subtitle && (
              <Typography variant="caption" color="text.secondary">
                {subtitle}
              </Typography>
            )}
          </Box>
          {headerExtra && <Box>{headerExtra}</Box>}
        </Box>
      )}
      <Box sx={{ p: 0 }}>{children}</Box>
    </Paper>
  );
};

export default Card;
