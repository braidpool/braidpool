// Theme types
export type ThemeType = 'dark' | 'light' | 'solarized';

// Base colors mapping for CSS variables
export const colors = {
  // Primary colors
  primary: 'var(--color-primary)',
  primaryLight: 'var(--color-primary-light)',

  // Secondary colors
  secondary: 'var(--color-secondary)',

  // Accent colors
  accent: 'var(--color-accent)',

  // Status colors
  warning: 'var(--color-warning)',

  // UI colors
  background: 'var(--color-background)',
  paper: 'var(--color-paper)',
  cardPaper: 'var(--color-card-paper)',
  surface: 'var(--color-surface)',
  surfaceHover: 'var(--color-surface-hover)',
  border: 'var(--color-border)',
  chartGrid: 'var(--color-chart-grid)',

  // Text colors
  textPrimary: 'var(--color-text-primary)',
  textSecondary: 'var(--color-text-secondary)',
  textDisabled: 'var(--color-text-disabled)',

  // Element colors
  buttonBackground: 'var(--color-button-background)',
  buttonBackgroundHover: 'var(--color-button-background-hover)',
  buttonText: 'var(--color-button-text)',

  // Card accent colors
  cardAccentSecondary: 'var(--color-card-accent-secondary)',

  // Special elements

  // DAG Visualization colors
  tipNode: 'var(--color-tip-node)',
  nodeStroke: 'var(--color-node-stroke)',
};

// Theme definitions
export const themes: Record<ThemeType, Record<string, string>> = {
  dark: {
    '--color-primary': '#3986e8',
    '--color-primary-light': '#64b5f6',
    '--color-secondary': '#ff9800',
    '--color-accent': '#ffc107',
    '--color-warning': '#ff9800',
    '--color-background': '#121212',
    '--color-paper': '#1e1e1e',
    '--color-card-paper': 'rgba(30, 30, 30, 1)',
    '--color-surface': '#2d2d2d',
    '--color-surface-hover': 'rgba(255,255,255,0.05)',
    '--color-border': 'rgba(255,255,255,0.05)',
    '--color-chart-grid': 'rgba(255,255,255,0.1)',
    '--color-text-primary': '#ffffff',
    '--color-text-secondary': '#b0b0b0',
    '--color-text-disabled': '#686868',
    '--color-button-background': '#2d2d2d',
    '--color-button-background-hover': '#3d3d3d',
    '--color-button-text': '#ffffff',
    '--color-card-accent-secondary': '#ff9800',
    '--color-tip-node': '#ff6b6b',
    '--color-node-stroke': '#ffffff',
  },
  light: {
    '--color-primary': '#3986e8',
    '--color-primary-light': '#64b5f6',
    '--color-secondary': '#ff9800',
    '--color-accent': '#ffc107',
    '--color-warning': '#f57c00',
    '--color-background': '#f5f5f5',
    '--color-paper': '#ffffff',
    '--color-card-paper': '#fcfcfc',
    '--color-surface': '#e8e8e8',
    '--color-surface-hover': 'rgba(0,0,0,0.05)',
    '--color-border': 'rgba(0,0,0,0.1)',
    '--color-chart-grid': 'rgba(0,0,0,0.1)',
    '--color-text-primary': '#121212',
    '--color-text-secondary': '#5f6368',
    '--color-text-disabled': '#9e9e9e',
    '--color-button-background': '#e0e0e0',
    '--color-button-background-hover': '#d5d5d5',
    '--color-button-text': '#000000',
    '--color-card-accent-secondary': '#ff9800',
    '--color-tip-node': '#ff6b6b',
    '--color-node-stroke': '#ffffff',
  },
  solarized: {
    '--color-primary': '#268bd2',
    '--color-primary-light': '#2aa198',
    '--color-secondary': '#b58900',
    '--color-accent': '#d33682',
    '--color-warning': '#b58900',
    '--color-background': '#002b36',
    '--color-paper': '#073642',
    '--color-card-paper': '#0a4052',
    '--color-surface': '#0a4052',
    '--color-surface-hover': 'rgba(147, 161, 161, 0.1)',
    '--color-border': 'rgba(147, 161, 161, 0.2)',
    '--color-chart-grid': 'rgba(147, 161, 161, 0.2)',
    '--color-text-primary': '#93a1a1',
    '--color-text-secondary': '#839496',
    '--color-text-disabled': '#586e75',
    '--color-button-background': '#073642',
    '--color-button-background-hover': '#586e75',
    '--color-button-text': '#93a1a1',
    '--color-card-accent-secondary': '#b58900',
    '--color-tip-node': '#dc322f',
    '--color-node-stroke': '#fdf6e3',
  },
};

export default colors;
