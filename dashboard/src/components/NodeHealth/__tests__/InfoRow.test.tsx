import { render, screen } from '@testing-library/react';
import { InfoRow } from '../InfoRow';

describe('InfoRow', () => {
  it('renders label and value', () => {
    render(<InfoRow label="Test Label" value="Test Value" />);
    expect(screen.getByText('Test Label')).toBeInTheDocument();
    expect(screen.getByText('Test Value')).toBeInTheDocument();
  });

  it('renders numeric value', () => {
    render(<InfoRow label="Blocks" value={1234} />);
    expect(screen.getByText('Blocks')).toBeInTheDocument();
    expect(screen.getByText('1234')).toBeInTheDocument();
  });
});
