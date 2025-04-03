import React from 'react';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import CssBaseline from '@mui/material/CssBaseline';
import { Box, Container, Link, Typography } from '@mui/material';
import Dashboard from './pages/Dashboard';

// Create a theme
const theme = createTheme({
  palette: {
    mode: 'light',
    primary: {
      main: '#1976d2',
    },
    secondary: {
      main: '#dc004e',
    },
  },
  components: {
    MuiContainer: {
      styleOverrides: {
        root: {
          paddingLeft: 16,
          paddingRight: 16,
          '@media (min-width: 600px)': {
            paddingLeft: 24,
            paddingRight: 24,
          },
        },
      },
    },
  },
});

function Copyright() {
  return (
    <Typography variant='body2' color='text.secondary' align='center'>
      {'© '}
      <Link color='inherit' href='https://github.com/braidpool/braidpool'>
        Braidpool
      </Link>{' '}
      {new Date().getFullYear()}
    </Typography>
  );
}

function App() {
  return (
    <ThemeProvider theme={theme}>
      <CssBaseline />
      <Box
        sx={{
          display: 'flex',
          flexDirection: 'column',
          minHeight: '100vh',
          backgroundColor: '#f8f9fa',
        }}>
        <Dashboard />
        <Box
          component='footer'
          sx={{
            py: 3,
            mt: 'auto',
            bgcolor: 'background.paper',
            borderTop: '1px solid rgba(0,0,0,0.05)',
          }}>
          <Container maxWidth='lg'>
            <Typography variant='body1' align='center' gutterBottom>
              A visualization dashboard for the Braidpool decentralized mining
              pool
            </Typography>
            <Copyright />
          </Container>
        </Box>
      </Box>
    </ThemeProvider>
  );
}

export default App;
