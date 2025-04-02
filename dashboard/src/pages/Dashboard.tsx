import React, { useEffect, useState } from 'react';
import {
  Container,
  Typography,
  Paper,
  Box,
  CircularProgress,
  Alert,
  Divider,
} from '@mui/material';
import BraidVisualization from '../components/BraidVisualization';
import BraidStats from '../components/BraidStats';
import { BraidVisualizationData } from '../types/braid';
import {
  loadSampleBraidData,
  transformBraidData,
} from '../utils/braidDataTransformer';

const Dashboard: React.FC = () => {
  const [data, setData] = useState<BraidVisualizationData | null>(null);
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const fetchData = async () => {
      try {
        console.log('🔄 Loading braid data...');
        setLoading(true);

        // In a real implementation, this would fetch from an API
        // For now, we'll use sample data
        const braidData = await loadSampleBraidData();
        setData(transformBraidData(braidData));
        console.log('✅ Data loaded successfully!');
        setLoading(false);
      } catch (err) {
        console.error('❌ Error loading data:', err);
        setError('Failed to load data. Please try again later.');
        setLoading(false);
      }
    };

    fetchData();
  }, []);

  if (loading) {
    return (
      <Container>
        <Box
          sx={{
            display: 'flex',
            justifyContent: 'center',
            alignItems: 'center',
            height: '50vh',
          }}>
          <CircularProgress />
          <Typography variant='h6' sx={{ ml: 2 }}>
            Loading Braid Data...
          </Typography>
        </Box>
      </Container>
    );
  }

  if (error) {
    return (
      <Container>
        <Alert severity='error' sx={{ mt: 4 }}>
          {error}
        </Alert>
      </Container>
    );
  }

  return (
    <Container maxWidth='xl'>
      <Box sx={{ my: 4 }}>
        <Typography variant='h4' component='h1' gutterBottom>
          Braidpool Dashboard
        </Typography>
        <Typography variant='subtitle1' color='text.secondary' paragraph>
          Visualize and analyze the structure of the Braidpool mining pool's
          braid data.
        </Typography>

        {data && (
          <>
            {/* Summary Section */}
            <Box sx={{ mb: 4 }}>
              <Typography variant='h5' sx={{ mb: 2 }}>
                Braid Summary
              </Typography>
              <Box sx={{ display: 'flex', flexWrap: 'wrap', gap: 3 }}>
                <Paper sx={{ p: 3, flex: '1 1 200px', minWidth: '200px' }}>
                  <Typography variant='subtitle2' color='text.secondary'>
                    Total Beads
                  </Typography>
                  <Typography variant='h4'>{data.nodes.length}</Typography>
                </Paper>
                <Paper sx={{ p: 3, flex: '1 1 200px', minWidth: '200px' }}>
                  <Typography variant='subtitle2' color='text.secondary'>
                    Total Cohorts
                  </Typography>
                  <Typography variant='h4'>{data.cohorts.length}</Typography>
                </Paper>
                <Paper sx={{ p: 3, flex: '1 1 200px', minWidth: '200px' }}>
                  <Typography variant='subtitle2' color='text.secondary'>
                    Nb/Nc Ratio
                  </Typography>
                  <Typography variant='h4'>
                    {(data.nodes.length / data.cohorts.length).toFixed(2)}
                  </Typography>
                </Paper>
                <Paper sx={{ p: 3, flex: '1 1 200px', minWidth: '200px' }}>
                  <Typography variant='subtitle2' color='text.secondary'>
                    Tip Beads
                  </Typography>
                  <Typography variant='h4'>
                    {data.nodes.filter((n) => n.isTip).length}
                  </Typography>
                </Paper>
              </Box>
            </Box>

            <Divider sx={{ my: 4 }} />

            {/* Visualization Section */}
            <Box sx={{ mb: 4 }}>
              <Typography variant='h5' sx={{ mb: 2 }}>
                Braid Structure Visualization
              </Typography>
              <Paper sx={{ p: 2, mb: 2 }}>
                <BraidVisualization
                  data={data}
                  width={
                    window.innerWidth > 1200 ? 1100 : window.innerWidth - 100
                  }
                  height={500}
                />
              </Paper>
              <Typography variant='body2' color='text.secondary'>
                The visualization shows the directed acyclic graph (DAG)
                structure of the braid. Nodes are color-coded by cohort, with
                high-work paths highlighted.
              </Typography>
            </Box>

            <Divider sx={{ my: 4 }} />

            {/* Statistics Section */}
            <Box>
              <Typography variant='h5' sx={{ mb: 2 }}>
                Detailed Statistics
              </Typography>
              <BraidStats data={data} />
            </Box>
          </>
        )}
      </Box>
    </Container>
  );
};

export default Dashboard;
