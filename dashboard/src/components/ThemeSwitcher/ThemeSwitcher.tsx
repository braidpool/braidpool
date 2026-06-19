import React, { useState } from 'react';
import {
  IconButton,
  Menu,
  MenuItem,
  ListItemIcon,
  ListItemText,
  Divider,
  Box,
  Dialog,
  DialogTitle,
  DialogContent,
  DialogActions,
  Button,
  TextField,
  Typography,
} from '@mui/material';
import {
  Brightness7 as LightIcon,
  Brightness4 as DarkIcon,
  WbSunny as SolarizedIcon,
  Palette as PaletteIcon,
  Settings as SettingsIcon,
  RestartAlt as ResetIcon,
} from '@mui/icons-material';
import { useTheme, ThemeMode, ThemeColors } from '../../contexts/ThemeContext';

const ThemeSwitcher: React.FC = () => {
  const { themeMode, setThemeMode, setCustomColors, resetTheme, themeConfig } = useTheme();
  const [anchorEl, setAnchorEl] = useState<null | HTMLElement>(null);
  const [colorDialogOpen, setColorDialogOpen] = useState(false);
  const [tempColors, setTempColors] = useState<Partial<ThemeColors>>({});

  const handleMenuOpen = (event: React.MouseEvent<HTMLElement>) => {
    setAnchorEl(event.currentTarget);
  };

  const handleMenuClose = () => {
    setAnchorEl(null);
  };

  const handleThemeChange = (mode: ThemeMode) => {
    setThemeMode(mode);
    handleMenuClose();
  };

  const handleColorDialogOpen = () => {
    setTempColors(themeConfig.colors);
    setColorDialogOpen(true);
    handleMenuClose();
  };

  const handleColorDialogClose = () => {
    setColorDialogOpen(false);
    setTempColors({});
  };

  const handleColorSave = () => {
    setCustomColors(tempColors);
    setColorDialogOpen(false);
    setTempColors({});
  };

  const handleReset = () => {
    resetTheme();
    handleMenuClose();
  };

  const getThemeIcon = () => {
    switch (themeMode) {
      case 'light':
        return <LightIcon />;
      case 'dark':
        return <DarkIcon />;
      case 'solarized':
        return <SolarizedIcon />;
      default:
        return <PaletteIcon />;
    }
  };

  return (
    <>
      <IconButton
        onClick={handleMenuOpen}
        color="inherit"
        aria-label="theme switcher"
        sx={{
          position: 'fixed',
          top: 16,
          right: 16,
          zIndex: 1000,
          backgroundColor: 'background.paper',
          '&:hover': {
            backgroundColor: 'background.paper',
          },
        }}
      >
        {getThemeIcon()}
      </IconButton>

      <Menu
        anchorEl={anchorEl}
        open={Boolean(anchorEl)}
        onClose={handleMenuClose}
        anchorOrigin={{
          vertical: 'bottom',
          horizontal: 'right',
        }}
        transformOrigin={{
          vertical: 'top',
          horizontal: 'right',
        }}
      >
        <MenuItem onClick={() => handleThemeChange('light')} selected={themeMode === 'light'}>
          <ListItemIcon>
            <LightIcon />
          </ListItemIcon>
          <ListItemText primary="Light Theme" />
        </MenuItem>
        <MenuItem onClick={() => handleThemeChange('dark')} selected={themeMode === 'dark'}>
          <ListItemIcon>
            <DarkIcon />
          </ListItemIcon>
          <ListItemText primary="Dark Theme" />
        </MenuItem>
        <MenuItem onClick={() => handleThemeChange('solarized')} selected={themeMode === 'solarized'}>
          <ListItemIcon>
            <SolarizedIcon />
          </ListItemIcon>
          <ListItemText primary="Solarized Theme" />
        </MenuItem>
        <Divider />
        <MenuItem onClick={handleColorDialogOpen}>
          <ListItemIcon>
            <PaletteIcon />
          </ListItemIcon>
          <ListItemText primary="Custom Colors" />
        </MenuItem>
        <MenuItem onClick={handleReset}>
          <ListItemIcon>
            <ResetIcon />
          </ListItemIcon>
          <ListItemText primary="Reset to Default" />
        </MenuItem>
      </Menu>

      <Dialog open={colorDialogOpen} onClose={handleColorDialogClose} maxWidth="sm" fullWidth>
        <DialogTitle>Custom Theme Colors</DialogTitle>
        <DialogContent>
          <Box sx={{ display: 'flex', flexDirection: 'column', gap: 2, mt: 2 }}>
            <Box>
              <Typography variant="subtitle2" gutterBottom>
                Primary Color
              </Typography>
              <TextField
                fullWidth
                type="color"
                value={tempColors.primary || themeConfig.colors.primary}
                onChange={(e) => setTempColors({ ...tempColors, primary: e.target.value })}
                InputProps={{
                  sx: { height: 56 },
                }}
              />
            </Box>
            <Box>
              <Typography variant="subtitle2" gutterBottom>
                Secondary Color
              </Typography>
              <TextField
                fullWidth
                type="color"
                value={tempColors.secondary || themeConfig.colors.secondary}
                onChange={(e) => setTempColors({ ...tempColors, secondary: e.target.value })}
                InputProps={{
                  sx: { height: 56 },
                }}
              />
            </Box>
            <Box>
              <Typography variant="subtitle2" gutterBottom>
                Background Color
              </Typography>
              <TextField
                fullWidth
                type="color"
                value={tempColors.background || themeConfig.colors.background}
                onChange={(e) => setTempColors({ ...tempColors, background: e.target.value })}
                InputProps={{
                  sx: { height: 56 },
                }}
              />
            </Box>
            <Box>
              <Typography variant="subtitle2" gutterBottom>
                Paper Color
              </Typography>
              <TextField
                fullWidth
                type="color"
                value={tempColors.paper || themeConfig.colors.paper}
                onChange={(e) => setTempColors({ ...tempColors, paper: e.target.value })}
                InputProps={{
                  sx: { height: 56 },
                }}
              />
            </Box>
          </Box>
        </DialogContent>
        <DialogActions>
          <Button onClick={handleColorDialogClose}>Cancel</Button>
          <Button onClick={handleColorSave} variant="contained">
            Apply Colors
          </Button>
        </DialogActions>
      </Dialog>
    </>
  );
};

export default ThemeSwitcher;
