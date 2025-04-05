import React from 'react';
import { Box, Typography, Paper, Divider } from '@mui/material';
import Card from './common/Card';
import colors from '../theme/colors';
import * as d3 from 'd3';

// Mock data for latency stats
const latencyData = [
  { time: '5m', value: 215 },
  { time: '10m', value: 223 },
  { time: '15m', value: 198 },
  { time: '20m', value: 205 },
  { time: '25m', value: 231 },
  { time: '30m', value: 227 },
  { time: '35m', value: 212 },
  { time: '40m', value: 219 },
  { time: '45m', value: 208 },
  { time: '50m', value: 201 },
  { time: '55m', value: 197 },
  { time: '60m', value: 203 },
];

// Mock data for mempool stats
const mempoolData = {
  size: '183.7 MB',
  txCount: '12,487',
  nextBlockFees: '0.00042 BTC',
  feeRates: {
    high: '21 sat/vB',
    medium: '14 sat/vB',
    low: '8 sat/vB',
  },
  feeEstimates: {
    fastest: '~10 min',
    fast: '~30 min',
    standard: '~1 hour',
    economy: '~3 hours',
  },
};

// StatItem component for displaying a statistic with label
const StatItem = ({
  label,
  value,
  color,
}: {
  label: string;
  value: string;
  color?: string;
}) => (
  <Box sx={{ mb: 2 }}>
    <Typography
      variant='body2'
      color='textSecondary'
      sx={{ fontSize: '0.8rem', mb: 0.5 }}>
      {label}
    </Typography>
    <Typography
      variant='h6'
      sx={{
        fontWeight: 500,
        color: color || colors.textPrimary,
        fontSize: '1.1rem',
      }}>
      {value}
    </Typography>
  </Box>
);

// Fee rate component for displaying fee levels
const FeeRate = ({
  level,
  rate,
  time,
}: {
  level: string;
  rate: string;
  time: string;
}) => (
  <Box sx={{ display: 'flex', justifyContent: 'space-between', mb: 1.5 }}>
    <Box sx={{ display: 'flex', alignItems: 'center' }}>
      <Box
        sx={{
          width: 8,
          height: 8,
          borderRadius: '50%',
          backgroundColor:
            level === 'Fastest'
              ? colors.error
              : level === 'Fast'
              ? colors.warning
              : level === 'Standard'
              ? colors.success
              : colors.textSecondary,
          mr: 1.5,
        }}
      />
      <Typography variant='body2' sx={{ fontSize: '0.85rem' }}>
        {level}
      </Typography>
    </Box>
    <Typography
      variant='body2'
      sx={{ fontSize: '0.85rem', color: colors.textSecondary }}>
      {rate}
    </Typography>
    <Typography
      variant='body2'
      sx={{ fontSize: '0.85rem', color: colors.textSecondary }}>
      {time}
    </Typography>
  </Box>
);

const MempoolLatencyStats = () => {
  return (
    <Card
      title='Network Performance'
      subtitle='Mempool stats and latency metrics'
      accentColor={colors.cardAccentPrimary}>
      <Box
        sx={{
          display: 'flex',
          flexDirection: { xs: 'column', md: 'row' },
          gap: 3,
        }}>
        {/* Mempool Stats */}
        <Box sx={{ flex: { xs: '1 1 100%', md: '1 1 50%' } }}>
          <Paper
            elevation={0}
            sx={{
              backgroundColor: colors.paper,
              borderRadius: 1,
              border: `1px solid ${colors.primary}20`,
              p: 2,
              height: '100%',
            }}>
            <Typography variant='h6' sx={{ mb: 2, fontWeight: 500 }}>
              Mempool Status
            </Typography>

            <Box sx={{ display: 'flex', flexWrap: 'wrap', mx: -1, mb: 2 }}>
              <Box sx={{ width: { xs: '50%', sm: '50%' }, p: 1 }}>
                <StatItem label='SIZE' value={mempoolData.size} />
              </Box>
              <Box sx={{ width: { xs: '50%', sm: '50%' }, p: 1 }}>
                <StatItem label='TRANSACTIONS' value={mempoolData.txCount} />
              </Box>
              <Box sx={{ width: { xs: '50%', sm: '50%' }, p: 1 }}>
                <StatItem
                  label='NEXT BLOCK FEES'
                  value={mempoolData.nextBlockFees}
                  color={colors.secondary}
                />
              </Box>
              <Box sx={{ width: { xs: '50%', sm: '50%' }, p: 1 }}>
                <StatItem
                  label='HIGH PRIORITY FEE'
                  value={mempoolData.feeRates.high}
                  color={colors.error}
                />
              </Box>
            </Box>

            <Divider sx={{ my: 2 }} />

            <Typography variant='subtitle2' sx={{ mb: 2, fontWeight: 500 }}>
              Fee Estimates
            </Typography>

            <FeeRate
              level='Fastest'
              rate={mempoolData.feeRates.high}
              time={mempoolData.feeEstimates.fastest}
            />
            <FeeRate
              level='Fast'
              rate={mempoolData.feeRates.medium}
              time={mempoolData.feeEstimates.fast}
            />
            <FeeRate
              level='Standard'
              rate={mempoolData.feeRates.medium}
              time={mempoolData.feeEstimates.standard}
            />
            <FeeRate
              level='Economy'
              rate={mempoolData.feeRates.low}
              time={mempoolData.feeEstimates.economy}
            />
          </Paper>
        </Box>

        {/* Latency Stats */}
        <Box sx={{ flex: { xs: '1 1 100%', md: '1 1 50%' } }}>
          <Paper
            elevation={0}
            sx={{
              backgroundColor: colors.paper,
              borderRadius: 1,
              border: `1px solid ${colors.primary}20`,
              p: 2,
              height: '100%',
            }}>
            <Typography variant='h6' sx={{ mb: 2, fontWeight: 500 }}>
              Network Latency
            </Typography>

            <Box sx={{ mb: 2 }}>
              <Box sx={{ display: 'flex', justifyContent: 'space-between' }}>
                <Typography
                  variant='body2'
                  color='textSecondary'
                  sx={{ fontSize: '0.8rem' }}>
                  Current:{' '}
                  <span style={{ color: colors.textPrimary, fontWeight: 500 }}>
                    203 ms
                  </span>
                </Typography>
                <Typography
                  variant='body2'
                  color='textSecondary'
                  sx={{ fontSize: '0.8rem' }}>
                  Avg (1h):{' '}
                  <span style={{ color: colors.textPrimary, fontWeight: 500 }}>
                    211 ms
                  </span>
                </Typography>
                <Typography
                  variant='body2'
                  color='textSecondary'
                  sx={{ fontSize: '0.8rem' }}>
                  Best:{' '}
                  <span style={{ color: colors.success, fontWeight: 500 }}>
                    197 ms
                  </span>
                </Typography>
              </Box>
            </Box>

            {/* Latency Chart (simplified) */}
            <Box
              sx={{
                height: 200,
                mt: 3,
                position: 'relative',
                '&::before': {
                  content: '""',
                  position: 'absolute',
                  top: 0,
                  left: 0,
                  right: 0,
                  bottom: 0,
                  backgroundImage: `linear-gradient(to right, ${colors.chartGrid} 1px, transparent 1px), linear-gradient(to bottom, ${colors.chartGrid} 1px, transparent 1px)`,
                  backgroundSize: '20% 25%',
                  opacity: 0.2,
                },
              }}>
              {/* Line graph would be created with D3.js */}
              <svg width='100%' height='100%'>
                <path
                  d={`M 0,${
                    100 - ((latencyData[0].value - 190) / 50) * 100
                  } ${latencyData
                    .map((point, i) => {
                      const x = i * (100 / (latencyData.length - 1));
                      const y = 100 - ((point.value - 190) / 50) * 100;
                      return `L ${x},${y}`;
                    })
                    .join(' ')}`}
                  fill='none'
                  stroke={colors.primary}
                  strokeWidth='2'
                />
                {latencyData.map((point, i) => {
                  const x = i * (100 / (latencyData.length - 1));
                  const y = 100 - ((point.value - 190) / 50) * 100;
                  return (
                    <circle
                      key={i}
                      cx={`${x}%`}
                      cy={`${y}%`}
                      r='3'
                      fill={colors.primary}
                      stroke={colors.chartBackground}
                      strokeWidth='1'
                    />
                  );
                })}
              </svg>

              {/* Y-axis labels */}
              <Box
                sx={{
                  position: 'absolute',
                  left: 0,
                  top: 0,
                  bottom: 0,
                  display: 'flex',
                  flexDirection: 'column',
                  justifyContent: 'space-between',
                  pr: 1,
                }}>
                <Typography
                  variant='caption'
                  sx={{ fontSize: '0.7rem', color: colors.textSecondary }}>
                  240ms
                </Typography>
                <Typography
                  variant='caption'
                  sx={{ fontSize: '0.7rem', color: colors.textSecondary }}>
                  215ms
                </Typography>
                <Typography
                  variant='caption'
                  sx={{ fontSize: '0.7rem', color: colors.textSecondary }}>
                  190ms
                </Typography>
              </Box>

              {/* X-axis labels */}
              <Box
                sx={{
                  position: 'absolute',
                  left: 0,
                  right: 0,
                  bottom: -20,
                  display: 'flex',
                  justifyContent: 'space-between',
                }}>
                <Typography
                  variant='caption'
                  sx={{ fontSize: '0.7rem', color: colors.textSecondary }}>
                  60m
                </Typography>
                <Typography
                  variant='caption'
                  sx={{ fontSize: '0.7rem', color: colors.textSecondary }}>
                  30m
                </Typography>
                <Typography
                  variant='caption'
                  sx={{ fontSize: '0.7rem', color: colors.textSecondary }}>
                  5m
                </Typography>
              </Box>
            </Box>

            <Divider sx={{ my: 2 }} />

            <Box sx={{ display: 'flex', justifyContent: 'space-between' }}>
              <StatItem label='SWITCHING TIME' value='1.8s' />
              <StatItem label='LAMBDA' value='1.87' />
              <StatItem label='A PARAMETER' value='3.2' />
            </Box>
          </Paper>
        </Box>
      </Box>
    </Card>
  );
};

export default MempoolLatencyStats;
