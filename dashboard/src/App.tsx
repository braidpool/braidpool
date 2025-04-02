import React from 'react';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import CssBaseline from '@mui/material/CssBaseline';
import {
  Box,
  AppBar,
  Toolbar,
  Typography,
  Container,
  Link,
} from '@mui/material';
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
        sx={{ display: 'flex', flexDirection: 'column', minHeight: '100vh' }}>
        <AppBar position='static'>
          <Toolbar>
            <Typography variant='h6' component='div' sx={{ flexGrow: 1 }}>
              Braidpool Dashboard
            </Typography>
          </Toolbar>
        </AppBar>
        <Container component='main' sx={{ flexGrow: 1, mt: 2, mb: 2 }}>
          <Dashboard />
        </Container>
        <Box component='footer' sx={{ py: 3, bgcolor: 'background.paper' }}>
          <Container maxWidth='sm'>
            <Typography variant='body1' align='center'>
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
