import React, { createContext, useContext, useState, useEffect, ReactNode } from 'react';
import { ThemePreset, ThemeConfig, themePresets, createMuiTheme, getTailwindColors } from './themes';
import { Theme } from '@mui/material/styles';

interface ThemeContextType {
  theme: Theme;
  themeConfig: ThemeConfig;
  themePreset: ThemePreset;
  setThemePreset: (preset: ThemePreset) => void;
  setCustomColor: (color: string) => void;
  toggleMode: () => void;
  tailwindColors: ReturnType<typeof getTailwindColors>;
}

const ThemeContext = createContext<ThemeContextType | undefined>(undefined);

const STORAGE_KEY = 'braidpool-theme-preference';
const CUSTOM_COLOR_KEY = 'braidpool-custom-color';

export const ThemeProvider: React.FC<{ children: ReactNode }> = ({ children }) => {
  const [themePreset, setThemePresetState] = useState<ThemePreset>('dark');
  const [customColor, setCustomColorState] = useState<string>('#3986e8');
  const [themeConfig, setThemeConfig] = useState<ThemeConfig>(themePresets.dark);
  const [theme, setTheme] = useState<Theme>(createMuiTheme(themePresets.dark));

  // Load theme preference from localStorage on mount
  useEffect(() => {
    const savedPreset = localStorage.getItem(STORAGE_KEY) as ThemePreset;
    const savedCustomColor = localStorage.getItem(CUSTOM_COLOR_KEY);

    if (savedPreset && themePresets[savedPreset]) {
      setThemePresetState(savedPreset);
    }

    if (savedCustomColor) {
      setCustomColorState(savedCustomColor);
    }
  }, []);

  // Update theme when preset or custom color changes
  useEffect(() => {
    let config: ThemeConfig;

    if (themePreset === 'custom') {
      config = {
        ...themePresets.custom,
        primary: customColor,
      };
    } else {
      config = themePresets[themePreset];
    }

    setThemeConfig(config);
    setTheme(createMuiTheme(config));
  }, [themePreset, customColor]);

  const setThemePreset = (preset: ThemePreset) => {
    setThemePresetState(preset);
    localStorage.setItem(STORAGE_KEY, preset);
  };

  const setCustomColor = (color: string) => {
    setCustomColorState(color);
    localStorage.setItem(CUSTOM_COLOR_KEY, color);
    if (themePreset !== 'custom') {
      setThemePreset('custom');
    }
  };

  const toggleMode = () => {
    const newMode = themeConfig.mode === 'dark' ? 'light' : 'dark';
    const newConfig: ThemeConfig = {
      ...themeConfig,
      mode: newMode,
      background: newMode === 'dark' ? '#121212' : '#f5f5f5',
      paper: newMode === 'dark' ? '#1e1e1e' : '#ffffff',
      textPrimary: newMode === 'dark' ? '#ffffff' : '#212121',
      textSecondary: newMode === 'dark' ? '#b0b0b0' : '#666666',
    };
    
    setThemeConfig(newConfig);
    setTheme(createMuiTheme(newConfig));
    
    // Update the preset to custom since we're modifying it
    if (themePreset !== 'custom') {
      setThemePreset('custom');
    }
  };

  const tailwindColors = getTailwindColors(themeConfig);

  return (
    <ThemeContext.Provider
      value={{
        theme,
        themeConfig,
        themePreset,
        setThemePreset,
        setCustomColor,
        toggleMode,
        tailwindColors,
      }}
    >
      {children}
    </ThemeContext.Provider>
  );
};

export const useTheme = () => {
  const context = useContext(ThemeContext);
  if (context === undefined) {
    throw new Error('useTheme must be used within a ThemeProvider');
  }
  return context;
};
