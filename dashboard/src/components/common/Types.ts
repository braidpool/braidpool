import { ReactNode } from 'react';
import { Page } from '../Dashboard/Types';

export interface CardProps {
  title?: ReactNode;
  subtitle?: ReactNode;
  children: ReactNode;
  accentColor?: string;
  headerExtra?: ReactNode;
}

export type HeaderNavProps = {
  title?: string;
  currentPage: Page;
  setCurrentPage: (page: Page) => void;
};
