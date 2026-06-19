import { PaletteMode } from '@mui/material';
import { createTheme } from '@mui/material/styles';

export type ThemePreset = 'dark' | 'light' | 'solarized' | 'custom';

export interface ThemeConfig {
  mode: PaletteMode;
  primary: string;
  secondary: string;
  background: string;
  paper: string;
  textPrimary: string;
  textSecondary: string;
}

export const themePresets: Record<ThemePreset, ThemeConfig> = {
  dark: {
    mode: 'dark',
    primary: '#3986e8',
    secondary: '#dc004e',
    background: '#121212',
    paper: '#1e1e1e',
    textPrimary: '#ffffff',
    textSecondary: '#b0b0b0',
  },
  light: {
    mode: 'light',
    primary: '#3986e8',
    secondary: '#dc004e',
    background: '#f5f5f5',
    paper: '#ffffff',
    textPrimary: '#212121',
    textSecondary: '#666666',
  },
  solarized: {
    mode: 'light',
    primary: '#268bd2',
    secondary: '#cb4b16',
    background: '#fdf6e3',
    paper: '#eee8d5',
    textPrimary: '#657b83',
    textSecondary: '#586e75',
  },
  custom: {
    mode: 'dark',
    primary: '#3986e8',
    secondary: '#dc004e',
    background: '#121212',
    paper: '#1e1e1e',
    textPrimary: '#ffffff',
    textSecondary: '#b0b0b0',
  },
};

export const colorPresets = [
  { name: 'Blue', value: '#3986e8' },
  { name: 'Purple', value: '#9c27b0' },
  { name: 'Green', value: '#4caf50' },
  { name: 'Orange', value: '#ff9800' },
  { name: 'Red', value: '#f44336' },
  { name: 'Teal', value: '#009688' },
  { name: 'Indigo', value: '#3f51b5' },
  { name: 'Pink', value: '#e91e63' },
];

export const createMuiTheme = (config: ThemeConfig) => {
  return createTheme({
    palette: {
      mode: config.mode,
      primary: {
        main: config.primary,
      },
      secondary: {
        main: config.secondary,
      },
      background: {
        default: config.background,
        paper: config.paper,
      },
      text: {
        primary: config.textPrimary,
        secondary: config.textSecondary,
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
};

export const getTailwindColors = (config: ThemeConfig) => {
  const isDark = config.mode === 'dark';
  return {
    primary: config.primary,
    secondary: config.secondary,
    background: config.background,
    paper: config.paper,
    text: {
      primary: config.textPrimary,
      secondary: config.textSecondary,
    },
    border: isDark ? 'rgba(255,255,255,0.08)' : 'rgba(0,0,0,0.12)',
    shadow: isDark ? 'rgba(0,0,0,0.25)' : 'rgba(0,0,0,0.1)',
  };
};
