import React, { useState } from 'react';
import { ThemeProvider } from '@mui/material/styles';
import CssBaseline from '@mui/material/CssBaseline';
import { Box, Container, Link, Typography, Button } from '@mui/material';
import { BrowserRouter, Routes, Route } from 'react-router-dom';
import Dashboard from './components/Dashboard/Dashboard';
import ShareDetails from './components/ShareDetails/ShareDetails';
import MinedSharesExplorer from './components/MinerDashboard/MinedSharesExplorer';
import { ThemeProvider as CustomThemeProvider, useTheme } from './contexts/ThemeContext';
import ThemeSwitcher from './components/ThemeSwitcher/ThemeSwitcher';

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

function AppContent() {
  const [shareDetailsOpen, setShareDetailsOpen] = useState(false);
  const { muiTheme } = useTheme();

  return (
    <ThemeProvider theme={muiTheme}>
      <CssBaseline />
      <BrowserRouter>
        <Box sx={{ display: 'flex' }}>
          <ThemeSwitcher />

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
              backgroundColor: 'background.default',
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
              <Container maxWidth="lg">
                <Typography variant="body1" align="center" gutterBottom>
                  A visualization dashboard for the Braidpool decentralized
                  mining pool
                </Typography>
                <Copyright />
              </Container>
            </Box>
          </Box>
        </Box>
      </BrowserRouter>
    </ThemeProvider>
  );
}

function App() {
  return (
    <CustomThemeProvider>
      <AppContent />
    </CustomThemeProvider>
  );
}

export default App;
