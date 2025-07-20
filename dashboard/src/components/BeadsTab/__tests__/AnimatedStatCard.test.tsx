import { render, screen } from '@testing-library/react';
import AnimatedStatCard from '../AnimatedStatCard';
import '@testing-library/jest-dom';

describe('<AnimatedStatCard />', () => {
  it('renders without crashing', () => {
    render(<AnimatedStatCard title="Blocks Found" value="10" />);
    const title = screen.getByText(/Blocks Found/i);
    const value = screen.getByText(/10/);
    expect(title).toBeInTheDocument();
    expect(value).toBeInTheDocument();
  });

  it('renders correct title and value', () => {
    render(<AnimatedStatCard title="Hashrate" value="215.32 TH/s" />);
    expect(screen.getByText('Hashrate')).toBeInTheDocument();
    expect(screen.getByText('215.32 TH/s')).toBeInTheDocument();
  });

  it('renders with empty title and value safely', () => {
    render(<AnimatedStatCard title="" value="" />);
    expect(screen.getByText('')).toBeInTheDocument();
  });

  it('handles null or undefined props gracefully in case data is still loading', () => {
    render(<AnimatedStatCard title={null as any} value={undefined as any} />);
    const card = screen.getByRole('generic'); // fallback match
    expect(card).toBeInTheDocument();
  });

  it('renders long strings correctly', () => {
    const longTitle = 'Total Transaction Volume in the Last 24 Hours';
    const longValue = '1,234,567,890.123456789 BTC';
    render(<AnimatedStatCard title={longTitle} value={longValue} />);
    expect(screen.getByText(longTitle)).toBeInTheDocument();
    expect(screen.getByText(longValue)).toBeInTheDocument();
  });

  it('has correct Tailwind classes applied', () => {
    const { container } = render(
      <AnimatedStatCard title="Ping" value="42ms" />
    );
    const rootDiv = container.firstChild as HTMLElement;
    expect(rootDiv.className).toMatch(/rounded-xl/);
    expect(rootDiv.className).toMatch(/bg-\[#1c1c1c\]/);
    expect(rootDiv.className).toMatch(/border-gray-700/);
    expect(rootDiv.className).toMatch(/hover:shadow-2xl/);
  });
});
