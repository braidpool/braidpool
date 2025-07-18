import { render, screen, fireEvent } from '@testing-library/react';
import { BeadRewardTooltip } from '../BeadRewardTooltip';

describe('<BeadRewardTooltip />', () => {
  const reward = 0.015; // BTC
  const mBTC = (reward * 1000).toFixed(2); // "15.00"

  it('renders reward in mBTC format', () => {
    render(<BeadRewardTooltip reward={reward} />);
    expect(screen.getByText(`${mBTC} mBTC`)).toBeInTheDocument();
  });

  it('shows tooltip on mouse enter', () => {
    render(<BeadRewardTooltip reward={reward} />);
    const trigger = screen.getByText(`${mBTC} mBTC`);

    fireEvent.mouseEnter(trigger);

    expect(screen.getAllByText(`${mBTC} mBTC`).length).toBeGreaterThan(1); // label + tooltip
  });

  it('hides tooltip on mouse leave', () => {
    render(<BeadRewardTooltip reward={reward} />);
    const trigger = screen.getByText(`${mBTC} mBTC`);

    fireEvent.mouseEnter(trigger);
    expect(screen.getAllByText(`${mBTC} mBTC`).length).toBeGreaterThan(1);

    fireEvent.mouseLeave(trigger);
    expect(screen.getAllByText(`${mBTC} mBTC`).length).toBe(1); // Only label remains
  });

  it('toggles tooltip on click (mobile support)', () => {
    render(<BeadRewardTooltip reward={reward} />);
    const trigger = screen.getByText(`${mBTC} mBTC`);

    fireEvent.click(trigger);
    expect(screen.getAllByText(`${mBTC} mBTC`).length).toBeGreaterThan(1);

    fireEvent.click(trigger);
    expect(screen.getAllByText(`${mBTC} mBTC`).length).toBe(1);
  });

  it('renders tooltip with correct styling class', () => {
    render(<BeadRewardTooltip reward={reward} />);
    const trigger = screen.getByText(`${mBTC} mBTC`);
    fireEvent.mouseEnter(trigger);

    const tooltip = screen.getAllByText(`${mBTC} mBTC`)[1];
    expect(tooltip).toHaveClass('absolute');
    expect(tooltip).toHaveClass('bg-gray-900/95');
    expect(tooltip).toHaveClass('rounded-lg');
  });
});
