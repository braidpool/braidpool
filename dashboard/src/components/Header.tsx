import React, { useState } from 'react';
import { AppBar, Box, Toolbar, Typography, Button } from '@mui/material';
import MenuIcon from '@mui/icons-material/Menu';
import SettingsIcon from '@mui/icons-material/Settings';
import NotificationsIcon from '@mui/icons-material/Notifications';
import FilterListIcon from '@mui/icons-material/FilterList';
import HomeIcon from '@mui/icons-material/Home';
import ActionIconButton from './common/ActionIconButton';
import colors from '../theme/colors';

interface HeaderProps {
  title?: string;
}

const Header: React.FC<HeaderProps> = ({ title = 'BRAIDPOOL' }) => {
  const [notificationCount] = useState<number>(3); // Mock notification count

  // Mock function to add miner
  const handleAddMiner = () => {
    console.log('🔌 Adding new miner...');
    // In real implementation, this would open a dialog to add a new miner
  };

  return (
    <AppBar
      position='fixed'
      elevation={0}
      sx={{
        backgroundColor: '#1a1a1a',
        boxShadow: `0 2px 4px rgba(0,0,0,0.3)`,
        height: 56,
        zIndex: (theme) => theme.zIndex.drawer + 1,
        borderBottom: '1px solid rgba(255,255,255,0.1)',
      }}>
      <Toolbar
        sx={{
          minHeight: 56,
          height: 56,
          px: { xs: 2, sm: 3 },
          py: 0,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'space-between',
          position: 'relative',
        }}>
        {/* Left side - Logo and Brand */}
        <Box
          sx={{
            display: 'flex',
            alignItems: 'center',
            height: '100%',
            my: 'auto',
          }}>
          <Box
            component='div'
            sx={{
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
              color: colors.textLight,
              bgcolor: colors.primary,
              borderRadius: '50%',
              width: 36,
              height: 36,
              mr: 2,
              fontSize: '1.1rem',
              fontWeight: 'bold',
              boxShadow: '0 1px 3px rgba(0,0,0,0.3)',
              flexShrink: 0,
              transform: 'translateY(-1px)', // Subtle adjustment to visually center
            }}>
            B
          </Box>
          <Typography
            variant='body1'
            component='div'
            sx={{
              fontWeight: 'bold',
              color: colors.textLight,
              letterSpacing: '0.5px',
              fontSize: '1.1rem',
              lineHeight: 1,
              mr: 2,
              whiteSpace: 'nowrap',
              transform: 'translateY(-1px)', // Subtle adjustment to visually center
            }}>
            {title}
          </Typography>
          <Box
            sx={{
              display: { xs: 'none', md: 'flex' },
              borderLeft: '1px solid rgba(255,255,255,0.2)',
              height: 28,
              mx: 2,
              transform: 'translateY(-1px)', // Subtle adjustment to visually center
            }}
          />
          <Box
            component='span'
            sx={{
              display: { xs: 'none', md: 'flex' },
              alignItems: 'center',
              color: colors.textLight,
              fontSize: '0.9rem',
              fontWeight: 500,
              ml: 0.5,
              transform: 'translateY(-1px)', // Subtle adjustment to visually center
            }}>
            <MenuIcon sx={{ fontSize: '1.2rem', mr: 1 }} />
          </Box>
        </Box>

        {/* Right side - Actions */}
        <Box
          sx={{
            display: 'flex',
            alignItems: 'center',
            gap: 1.5,
            height: '100%',
            transform: 'translateY(-1px)', // Subtle adjustment to visually center
          }}>
          <Button
            variant='contained'
            size='small'
            onClick={handleAddMiner}
            sx={{
              textTransform: 'none',
              px: { xs: 1.5, sm: 2 },
              py: 0.75,
              height: 34,
              backgroundColor: colors.accent,
              color: '#000',
              fontWeight: 500,
              fontSize: '0.875rem',
              borderRadius: 1.5,
              minWidth: 'auto',
              boxShadow: '0 1px 2px rgba(0,0,0,0.3)',
              '&:hover': {
                backgroundColor: colors.accentDark,
                boxShadow: '0 2px 4px rgba(0,0,0,0.3)',
              },
            }}>
            Add Miner
          </Button>

          <Box
            sx={{
              display: 'flex',
              alignItems: 'center',
              gap: 1,
              height: '100%',
            }}>
            <ActionIconButton
              icon={
                <HomeIcon
                  sx={{ fontSize: '1.2rem', color: colors.textLight }}
                />
              }
            />

            <ActionIconButton
              icon={
                <FilterListIcon
                  sx={{ fontSize: '1.2rem', color: colors.textLight }}
                />
              }
            />

            <Box sx={{ position: 'relative' }}>
              <ActionIconButton
                icon={
                  <NotificationsIcon
                    sx={{ fontSize: '1.2rem', color: colors.textLight }}
                  />
                }
              />
              {notificationCount > 0 && (
                <Box
                  sx={{
                    position: 'absolute',
                    top: -2,
                    right: -2,
                    bgcolor: colors.notification,
                    color: colors.textLight,
                    borderRadius: '50%',
                    width: 16,
                    height: 16,
                    fontSize: 10,
                    fontWeight: 'bold',
                    display: 'flex',
                    alignItems: 'center',
                    justifyContent: 'center',
                    border: '1.5px solid #1a1a1a',
                    boxShadow: '0 1px 2px rgba(0,0,0,0.3)',
                  }}>
                  {notificationCount}
                </Box>
              )}
            </Box>

            <ActionIconButton
              icon={
                <SettingsIcon
                  sx={{ fontSize: '1.2rem', color: colors.textLight }}
                />
              }
            />
          </Box>
        </Box>
      </Toolbar>
    </AppBar>
  );
};

export default Header;
