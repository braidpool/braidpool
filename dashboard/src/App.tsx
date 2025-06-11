import React, { useState } from 'react';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import CssBaseline from '@mui/material/CssBaseline';
import { Box, Container, Link, Typography, Button } from '@mui/material';
import { BrowserRouter, Routes, Route } from 'react-router-dom';
import Dashboard from './components/Dashboard/Dashboard';

import MinedSharesExplorer from './components/BeadsTab/MinedSharesExplorer';
import Footer from './components/Footer';

// Create a dark theme
const theme = createTheme({
  palette: {
    mode: 'dark',
    primary: {
      main: '#3986e8',
    },
    secondary: {
      main: '#dc004e',
    },
    background: {
      default: '#121212',
      paper: '#1e1e1e',
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
    <Typography variant="body2" color="text.secondary" align="center">
      {'© '}
      <Link color="inherit" href="https://github.com/braidpool/braidpool">
        Braidpool
      </Link>{' '}
      {new Date().getFullYear()}
      {' - Built with Vite 🚀'}
    </Typography>
  );
}

function App() {
  const [shareDetailsOpen, setShareDetailsOpen] = useState(false);

  return (
    <ThemeProvider theme={theme}>
      <CssBaseline />
      <BrowserRouter>
        <Box sx={{ display: 'flex' }}>
          {/* Test button for ShareDetails */}
          {/* <Button
            variant='contained'
            color='primary'
            onClick={() => setShareDetailsOpen(true)}
            sx={{
              position: 'fixed',
              top: '20px',
              right: '20px',
              zIndex: 9999,
            }}>
            Test Share Details
          </Button> */}

          {/* ShareDetails component */}
          {/* <ShareDetails
            open={shareDetailsOpen}
            onClose={() => setShareDetailsOpen(false)}
          /> */}

          <Box
            sx={{
              display: 'flex',
              flexDirection: 'column',
              minHeight: '100vh',
              backgroundColor: '#121212',
              width: '100%',
            }}
          >
            <Routes>
              <Route path="/" element={<Dashboard />} />
              <Route
                path="/minedsharesexplorer"
                element={<MinedSharesExplorer />}
              />
              {/* Add more routes as needed */}
            </Routes>
            <Box
              component="footer"
              sx={{
                py: 3,
                mt: 'auto',
                bgcolor: 'background.paper',
                borderTop: '1px solid rgba(255,255,255,0.05)',
              }}
            >
              {/* <Container maxWidth="lg">
                <Typography variant="body1" align="center" gutterBottom>
                  A visualization dashboard for the Braidpool decentralized
                  mining pool
                </Typography>
                <Copyright />
              </Container> */}
              <Footer></Footer>
            </Box>
          </Box>
        </Box>
      </BrowserRouter>
    </ThemeProvider>
  );
}

export default App;
