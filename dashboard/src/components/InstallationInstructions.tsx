import React from 'react';
import {
  Box,
  Typography,
  Paper,
  List,
  ListItem,
  ListItemIcon,
  ListItemText,
  Divider,
  Button,
} from '@mui/material';
import Card from './common/Card';
import colors from '../theme/colors';
import PlayCircleOutlineIcon from '@mui/icons-material/PlayCircleOutline';
import CodeIcon from '@mui/icons-material/Code';
import CloudDownloadIcon from '@mui/icons-material/CloudDownload';
import TerminalIcon from '@mui/icons-material/Terminal';
import ArrowForwardIcon from '@mui/icons-material/ArrowForward';

const InstallationInstructions = () => {
  return (
    <Card
      title='Installation Instructions'
      subtitle='How to install and set up Braidpool'
      accentColor={colors.cardAccentPrimary}>
      <Box
        sx={{
          display: 'flex',
          flexDirection: { xs: 'column', md: 'row' },
          gap: 3,
        }}>
        <Box sx={{ flex: { xs: '1 1 100%', md: '1 1 50%' } }}>
          <Paper
            elevation={0}
            sx={{
              backgroundColor: colors.paper,
              borderRadius: 1,
              border: `1px solid ${colors.border}`,
              p: 2,
              height: '100%',
            }}>
            <Typography variant='h6' sx={{ mb: 2, fontWeight: 500 }}>
              Basic Installation
            </Typography>

            <Typography variant='body2' sx={{ mb: 3 }}>
              Follow these steps to install and run Braidpool node on your
              system. Make sure you have the prerequisites installed before
              proceeding.
            </Typography>

            <List sx={{ pl: 0 }}>
              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <CloudDownloadIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Clone the repository'
                  secondary='git clone https://github.com/braidpool/braidpool.git'
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                    },
                  }}
                />
              </ListItem>

              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <TerminalIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Build the node'
                  secondary='cd node && cargo build'
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                    },
                  }}
                />
              </ListItem>

              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <PlayCircleOutlineIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Run the first seed node'
                  secondary='cargo run -- --bind=localhost:8989 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332'
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                      overflowX: 'auto',
                    },
                  }}
                />
              </ListItem>
            </List>

            <Box sx={{ mt: 3, display: 'flex', justifyContent: 'center' }}>
              <Button
                variant='contained'
                color='primary'
                startIcon={<CodeIcon />}
                sx={{ textTransform: 'none' }}
                onClick={() => console.log('📝 Opening full documentation...')}>
                View Full Documentation
              </Button>
            </Box>
          </Paper>
        </Box>

        <Box sx={{ flex: { xs: '1 1 100%', md: '1 1 50%' } }}>
          <Paper
            elevation={0}
            sx={{
              backgroundColor: colors.paper,
              borderRadius: 1,
              border: `1px solid ${colors.border}`,
              p: 2,
              height: '100%',
            }}>
            <Typography variant='h6' sx={{ mb: 2, fontWeight: 500 }}>
              CPUnet Testing Node
            </Typography>

            <Typography variant='body2' sx={{ mb: 3 }}>
              For testing purposes, you can set up the CPUnet testing node using
              nix-script from the root directory.
            </Typography>

            <List sx={{ pl: 0 }}>
              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <TerminalIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Build the nix-script'
                  secondary='nix-build cpunet_node.nix'
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                    },
                  }}
                />
              </ListItem>

              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <ArrowForwardIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Navigate to result directory'
                  secondary='cd result'
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                    },
                  }}
                />
              </ListItem>

              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <PlayCircleOutlineIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Run the CPUnet node'
                  secondary='./bin/bitcoind -cpunet -zmqpubsequence=tcp://127.0.0.1:28338'
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                    },
                  }}
                />
              </ListItem>

              <ListItem sx={{ px: 0, py: 1 }}>
                <ListItemIcon sx={{ minWidth: 36, color: colors.primary }}>
                  <TerminalIcon fontSize='small' />
                </ListItemIcon>
                <ListItemText
                  primary='Generate blocks'
                  secondary="./contrib/cpunet/miner --cli=./bin/bitcoin-cli --ongoing --address `./bin/bitcoin-cli -cpunet getnewaddress` --grind-cmd='./bin/bitcoin-util -cpunet -ntasks=1 grind'"
                  primaryTypographyProps={{
                    fontSize: '0.9rem',
                    fontWeight: 500,
                    color: colors.textPrimary,
                  }}
                  secondaryTypographyProps={{
                    fontSize: '0.8rem',
                    color: colors.textSecondary,
                    sx: {
                      backgroundColor: 'rgba(0,0,0,0.2)',
                      padding: '4px 8px',
                      mt: 0.5,
                      borderRadius: 1,
                      fontFamily: 'monospace',
                      overflowX: 'auto',
                    },
                  }}
                />
              </ListItem>
            </List>

            <Divider sx={{ my: 2 }} />

            <Typography variant='subtitle2' sx={{ mb: 1, fontWeight: 500 }}>
              Prerequisites
            </Typography>

            <List dense>
              <ListItem sx={{ px: 0, py: 0.5 }}>
                <Typography variant='body2' sx={{ fontSize: '0.85rem' }}>
                  • Rust toolchain (rustc, cargo)
                </Typography>
              </ListItem>
              <ListItem sx={{ px: 0, py: 0.5 }}>
                <Typography variant='body2' sx={{ fontSize: '0.85rem' }}>
                  • Nix package manager (for CPUnet)
                </Typography>
              </ListItem>
              <ListItem sx={{ px: 0, py: 0.5 }}>
                <Typography variant='body2' sx={{ fontSize: '0.85rem' }}>
                  • Bitcoin Core (for RPC and ZMQ access)
                </Typography>
              </ListItem>
            </List>
          </Paper>
        </Box>
      </Box>
    </Card>
  );
};

export default InstallationInstructions;
