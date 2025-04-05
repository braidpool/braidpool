import React, { useState, useEffect, ReactElement } from 'react';
import {
  Box,
  Typography,
  Chip,
  Tooltip,
  keyframes,
  alpha,
} from '@mui/material';
import { BraidVisualizationData } from '../types/braid';
import UpdateIcon from '@mui/icons-material/Update';
import TrendingUpIcon from '@mui/icons-material/TrendingUp';
import TrendingDownIcon from '@mui/icons-material/TrendingDown';
import SignalCellularAltIcon from '@mui/icons-material/SignalCellularAlt';
import MemoryIcon from '@mui/icons-material/Memory';
import HubIcon from '@mui/icons-material/Hub';
import GridViewIcon from '@mui/icons-material/GridView';
import Card from './common/Card';
import colors from '../theme/colors';
import { formatTime } from '../utils/formatters';

const pulse = keyframes`
  0% {
    opacity: 1;
  }
  50% {
    opacity: 0.6;
  }
  100% {
    opacity: 1;
  }
`;

interface BraidStatsProps {
  data: BraidVisualizationData;
}

const BraidStats: React.FC<BraidStatsProps> = ({ data }) => {
  // Calculate some basic statistics
  const totalNodes = data.nodes.length;
  const totalLinks = data.links.length;
  const totalCohorts = data.cohorts.length;
  const avgNodesPerCohort = (totalNodes / totalCohorts).toFixed(2);
  const tips = data.nodes.filter((node) => node.isTip);
  const nodesToLinkRatio = (totalNodes / totalLinks).toFixed(2);

  // Calculate average children per node (excluding tips)
  const nonTipNodes = data.nodes.filter((node) => !node.isTip);
  const totalChildren = nonTipNodes.reduce(
    (sum, node) => sum + node.children.length,
    0
  );
  const avgChildrenPerNode =
    nonTipNodes.length > 0
      ? (totalChildren / nonTipNodes.length).toFixed(2)
      : '0';

  // Calculate Nb/Nc ratio (total beads / total cohorts)
  const nbNcRatio = (totalNodes / totalCohorts).toFixed(3);

  // State for simulating live updates
  const [lastUpdated, setLastUpdated] = useState(new Date());
  const [trends, setTrends] = useState({
    totalNodes: 0,
    totalLinks: 0,
    totalCohorts: 0,
    tipBeads: 0,
  });

  // Simulate periodic updates to make the real-time aspect more apparent
  useEffect(() => {
    const intervalId = setInterval(() => {
      setLastUpdated(new Date());
      // Generate random trends for visual indication
      setTrends({
        totalNodes:
          Math.random() > 0.5 ? Math.random() * 0.05 : -Math.random() * 0.05,
        totalLinks:
          Math.random() > 0.5 ? Math.random() * 0.05 : -Math.random() * 0.05,
        totalCohorts: Math.random() > 0.7 ? 0.01 : 0,
        tipBeads:
          Math.random() > 0.6 ? Math.random() * 0.1 : -Math.random() * 0.1,
      });

      console.log(
        '🔄 Updated braid statistics at:',
        new Date().toLocaleTimeString()
      );
    }, 10000); // Update every 10 seconds

    return () => clearInterval(intervalId);
  }, []);

  // Format the last updated time
  const formattedTime = formatTime(lastUpdated);

  // Function to render a metric with icon and trend indicator
  const renderMetric = (
    label: string,
    value: string | number,
    trend: number,
    icon: ReactElement
  ): ReactElement => {
    const TrendIcon =
      trend > 0 ? TrendingUpIcon : trend < 0 ? TrendingDownIcon : null;
    const trendColor =
      trend > 0 ? '#4caf50' : trend < 0 ? '#f44336' : 'inherit';

    return (
      <Box
        sx={{ display: 'flex', flexDirection: 'column', position: 'relative' }}>
        <Box sx={{ display: 'flex', alignItems: 'center', mb: 0.5 }}>
          <Box
            sx={{
              mr: 1,
              color: 'text.secondary',
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
            }}>
            {icon}
          </Box>
          <Typography variant='subtitle2' color='text.secondary'>
            {label}:
          </Typography>
        </Box>
        <Box sx={{ display: 'flex', alignItems: 'center' }}>
          <Typography variant='body1' fontWeight='bold'>
            {value}
          </Typography>
          {TrendIcon && (
            <Tooltip
              title={`${Math.abs(trend * 100).toFixed(2)}% ${
                trend > 0 ? 'increase' : 'decrease'
              }`}>
              <TrendIcon
                sx={{
                  fontSize: 16,
                  ml: 0.5,
                  color: trendColor,
                  animation: trend !== 0 ? `${pulse} 2s infinite` : 'none',
                }}
              />
            </Tooltip>
          )}
        </Box>
      </Box>
    );
  };

  console.log('📊 Calculating braid statistics:', {
    totalNodes,
    totalLinks,
    totalCohorts,
    tips: tips.length,
    nbNcRatio,
  });

  return (
    <Box
      sx={{
        height: 'auto',
        minHeight: '100%',
        overflow: 'visible',
        paddingBottom: '48px', // Add extra bottom padding to the entire component
      }}>
      <Box
        sx={{
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'space-between',
          px: 1,
          pt: 1,
          mb: 2,
        }}>
        <Typography variant='h5' sx={{ display: 'flex', alignItems: 'center' }}>
          Braid Statistics
          <Box
            sx={{
              display: 'inline-flex',
              alignItems: 'center',
              ml: 2,
              fontSize: '0.75rem',
              bgcolor: alpha(colors.info, 0.1),
              color: colors.primary,
              borderRadius: 1,
              px: 1,
              py: 0.5,
            }}>
            <UpdateIcon
              sx={{
                fontSize: 16,
                mr: 0.5,
                animation: `${pulse} 2s infinite`,
              }}
            />
            Live {formattedTime}
          </Box>
        </Typography>
      </Box>

      <Box sx={{ display: 'flex', flexWrap: 'wrap', px: 1, gap: 2 }}>
        {/* Key Metrics */}
        <Box sx={{ flexBasis: { xs: '100%', md: 'calc(50% - 8px)' } }}>
          <Card
            accentColor={colors.cardAccentPrimary}
            title={
              <Box sx={{ display: 'flex', alignItems: 'center' }}>
                <SignalCellularAltIcon sx={{ mr: 1, color: colors.primary }} />
                Key Metrics
              </Box>
            }>
            <Box sx={{ display: 'flex', flexWrap: 'wrap', gap: 2, p: 2 }}>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Total Beads',
                  totalNodes,
                  trends.totalNodes,
                  <MemoryIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Total Links',
                  totalLinks,
                  trends.totalLinks,
                  <HubIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Total Cohorts',
                  totalCohorts,
                  trends.totalCohorts,
                  <GridViewIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Tip Beads',
                  tips.length,
                  trends.tipBeads,
                  <MemoryIcon sx={{ fontSize: 18, color: colors.error }} />
                )}
              </Box>
            </Box>
          </Card>
        </Box>

        {/* Derived Metrics */}
        <Box sx={{ flexBasis: { xs: '100%', md: 'calc(50% - 8px)' } }}>
          <Card
            accentColor={colors.cardAccentSecondary}
            title={
              <Box sx={{ display: 'flex', alignItems: 'center' }}>
                <TrendingUpIcon sx={{ mr: 1, color: colors.secondaryDark }} />
                Derived Metrics
              </Box>
            }>
            <Box sx={{ display: 'flex', flexWrap: 'wrap', gap: 2, p: 2 }}>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Nb/Nc Ratio',
                  nbNcRatio,
                  0,
                  <MemoryIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Avg Beads Per Cohort',
                  avgNodesPerCohort,
                  0,
                  <MemoryIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Avg Children Per Bead',
                  avgChildrenPerNode,
                  0,
                  <MemoryIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
              <Box sx={{ width: 'calc(50% - 8px)' }}>
                {renderMetric(
                  'Nodes to Links Ratio',
                  nodesToLinkRatio,
                  0,
                  <HubIcon sx={{ fontSize: 18 }} />
                )}
              </Box>
            </Box>
          </Card>
        </Box>

        {/* Cohort Distribution */}
        <Box
          sx={{
            width: '100%',
            minHeight: '200px',
            mb: 5, // Add bottom margin to push content away from footer
          }}>
          <Card
            accentColor={colors.cardAccentSuccess}
            title={
              <Box sx={{ display: 'flex', alignItems: 'center' }}>
                <GridViewIcon sx={{ mr: 1, color: colors.success }} />
                Cohort Distribution
              </Box>
            }>
            <Box
              sx={{
                display: 'grid',
                gridTemplateColumns: {
                  xs: 'repeat(2, 1fr)',
                  sm: 'repeat(3, 1fr)',
                  md: 'repeat(4, 1fr)',
                  lg: 'repeat(5, 1fr)',
                },
                gap: 2,
                padding: '16px 16px 24px 16px',
                height: 'auto',
                overflow: 'visible',
                pb: 3, // Extra bottom padding inside the card
              }}>
              {data.cohorts.map((cohort, index) => (
                <Chip
                  key={index}
                  label={`Cohort ${index}: ${cohort.length} beads`}
                  color={
                    index === data.cohorts.length - 1 ? 'primary' : 'default'
                  }
                  variant={
                    index === data.cohorts.length - 1 ? 'filled' : 'outlined'
                  }
                  size='small'
                  sx={{
                    animation:
                      index === data.cohorts.length - 1
                        ? `${pulse} 2s infinite`
                        : 'none',
                    height: '32px',
                    width: '100%',
                    justifyContent: 'center',
                    fontSize: '0.8125rem',
                  }}
                />
              ))}
            </Box>
          </Card>
        </Box>
      </Box>
    </Box>
  );
};

export default BraidStats;
