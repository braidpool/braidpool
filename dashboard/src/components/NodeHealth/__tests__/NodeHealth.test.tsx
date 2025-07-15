import { render, screen } from '@testing-library/react';
import NodeHealth from '../NodeHealth';

describe('NodeHealth', () => {
  it('renders loading state initially', () => {
    render(<NodeHealth />);
    expect(screen.getByText(/Loading.../i)).toBeInTheDocument();
  });
});
