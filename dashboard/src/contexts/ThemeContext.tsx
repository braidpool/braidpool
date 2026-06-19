import React, { createContext, useContext, useState, useEffect, ReactNode } from 'react';
import { createTheme, Theme } from '@mui/material/styles';

export type ThemeMode = 'light' | 'dark' | 'solarized';

export interface ThemeColors {
  primary: string;
  secondary: string;
  background: string;
  paper: string;
}

export interface ThemeConfig {
  mode: ThemeMode;
  colors: ThemeColors;
}

const THEME_STORAGE_KEY = 'braidpool-theme-preference';

// Predefined theme configurations
const themeConfigs: Record<ThemeMode, ThemeConfig> = {
  light: {
    mode: 'light',
    colors: {
      primary: '#1976d2',
      secondary: '#dc004e',
      background: '#f5f5f5',
      paper: '#ffffff',
    },
  },
  dark: {
    mode: 'dark',
    colors: {
      primary: '#3986e8',
      secondary: '#dc004e',
      background: '#121212',
      paper: '#1e1e1e',
    },
  },
  solarized: {
    mode: 'light',
    colors: {
      primary: '#268bd2',
      secondary: '#d33682',
      background: '#fdf6e3',
      paper: '#eee8d5',
    },
  },
};

// Create MUI theme from config
const createMuiTheme = (config: ThemeConfig): Theme => {
  // MUI only supports 'light' or 'dark' modes, so map 'solarized' to 'light'
  const muiMode: 'light' | 'dark' = config.mode === 'solarized' ? 'light' : config.mode;
  
  return createTheme({
    palette: {
      mode: muiMode,
      primary: {
        main: config.colors.primary,
      },
      secondary: {
        main: config.colors.secondary,
      },
      background: {
        default: config.colors.background,
        paper: config.colors.paper,
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

interface ThemeContextType {
  themeMode: ThemeMode;
  themeConfig: ThemeConfig;
  muiTheme: Theme;
  setThemeMode: (mode: ThemeMode) => void;
  setCustomColors: (colors: Partial<ThemeColors>) => void;
  resetTheme: () => void;
}

const ThemeContext = createContext<ThemeContextType | undefined>(undefined);

export const ThemeProvider: React.FC<{ children: ReactNode }> = ({ children }) => {
  const [themeMode, setThemeModeState] = useState<ThemeMode>(() => {
    // Load from localStorage or default to dark
    const saved = localStorage.getItem(THEME_STORAGE_KEY);
    if (saved && (saved === 'light' || saved === 'dark' || saved === 'solarized')) {
      return saved as ThemeMode;
    }
    return 'dark';
  });

  const [customColors, setCustomColorsState] = useState<Partial<ThemeColors>>(() => {
    // Load custom colors from localStorage
    const saved = localStorage.getItem(`${THEME_STORAGE_KEY}-colors`);
    if (saved) {
      try {
        return JSON.parse(saved);
      } catch {
        return {};
      }
    }
    return {};
  });

  // Update localStorage when theme mode changes
  useEffect(() => {
    localStorage.setItem(THEME_STORAGE_KEY, themeMode);
  }, [themeMode]);

  // Update localStorage when custom colors change
  useEffect(() => {
    if (Object.keys(customColors).length > 0) {
      localStorage.setItem(`${THEME_STORAGE_KEY}-colors`, JSON.stringify(customColors));
    }
  }, [customColors]);

  const setThemeMode = (mode: ThemeMode) => {
    setThemeModeState(mode);
    // Clear custom colors when switching to a predefined theme
    setCustomColorsState({});
  };

  const setCustomColors = (colors: Partial<ThemeColors>) => {
    setCustomColorsState(prev => ({ ...prev, ...colors }));
  };

  const resetTheme = () => {
    setThemeModeState('dark');
    setCustomColorsState({});
  };

  // Merge predefined theme with custom colors
  const themeConfig: ThemeConfig = {
    ...themeConfigs[themeMode],
    colors: {
      ...themeConfigs[themeMode].colors,
      ...customColors,
    },
  };

  const muiTheme = createMuiTheme(themeConfig);

  return (
    <ThemeContext.Provider
      value={{
        themeMode,
        themeConfig,
        muiTheme,
        setThemeMode,
        setCustomColors,
        resetTheme,
      }}
    >
      {children}
    </ThemeContext.Provider>
  );
};

export const useTheme = (): ThemeContextType => {
  const context = useContext(ThemeContext);
  if (!context) {
    throw new Error('useTheme must be used within a ThemeProvider');
  }
  return context;
};
