import { ReactNode } from 'react';

export interface CardProps {
  title?: ReactNode;
  subtitle?: ReactNode;
  children: ReactNode;
  accentColor?: string;
  headerExtra?: ReactNode;
}
export interface HeaderProps {
  title?: string;
}

export interface KPICardProps {
  title: string;
  value: string | number;
  unit?: string;
  change?: number;
  subtitle?: string;
  loading?: boolean;
  info?: string;
  icon?: React.ReactNode;
}

export interface StatCardProps {
  title: string;
  value: string;
  icon?: React.ReactNode;
  loading?: boolean;
}

export interface TopStatsBarProps {
  loading?: boolean;
}
