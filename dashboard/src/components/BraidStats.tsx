import React from 'react';
import { Box, Card, CardContent, Typography, Chip } from '@mui/material';
import { BraidVisualizationData } from '../types/braid';

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

  // Calculate the connection density (actual links / possible links)
  const maxPossibleLinks = (totalNodes * (totalNodes - 1)) / 2;
  const connectionDensity = ((totalLinks / maxPossibleLinks) * 100).toFixed(2);

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

  console.log('📊 Calculating braid statistics:', {
    totalNodes,
    totalLinks,
    totalCohorts,
    tips: tips.length,
    nbNcRatio,
  });

  return (
    <Card sx={{ margin: 2 }}>
      <CardContent>
        <Typography variant='h5' gutterBottom>
          Braid Statistics
        </Typography>

        <Box sx={{ display: 'flex', flexWrap: 'wrap', gap: 2 }}>
          {/* Key Metrics */}
          <Box sx={{ flex: '1 1 45%', minWidth: '250px', mb: 2 }}>
            <Typography variant='h6' sx={{ mb: 1 }}>
              Key Metrics
            </Typography>
            <Box sx={{ display: 'flex', flexWrap: 'wrap' }}>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Total Beads:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {totalNodes}
                </Typography>
              </Box>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Total Links:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {totalLinks}
                </Typography>
              </Box>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Total Cohorts:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {totalCohorts}
                </Typography>
              </Box>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Tip Beads:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {tips.length}
                </Typography>
              </Box>
            </Box>
          </Box>

          {/* Derived Metrics */}
          <Box sx={{ flex: '1 1 45%', minWidth: '250px' }}>
            <Typography variant='h6' sx={{ mb: 1 }}>
              Derived Metrics
            </Typography>
            <Box sx={{ display: 'flex', flexWrap: 'wrap' }}>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Nb/Nc Ratio:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {nbNcRatio}
                </Typography>
              </Box>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Avg Beads Per Cohort:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {avgNodesPerCohort}
                </Typography>
              </Box>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Avg Children Per Bead:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {avgChildrenPerNode}
                </Typography>
              </Box>
              <Box sx={{ width: '50%', mb: 1 }}>
                <Typography variant='subtitle2' color='text.secondary'>
                  Nodes to Links Ratio:
                </Typography>
                <Typography variant='body1' fontWeight='bold'>
                  {nodesToLinkRatio}
                </Typography>
              </Box>
            </Box>
          </Box>

          {/* Cohort Distribution */}
          <Box sx={{ width: '100%' }}>
            <Typography variant='h6' sx={{ mb: 1 }}>
              Cohort Distribution
            </Typography>
            <Box sx={{ display: 'flex', flexWrap: 'wrap', gap: 1 }}>
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
                />
              ))}
            </Box>
          </Box>
        </Box>
      </CardContent>
    </Card>
  );
};

export default BraidStats;
