import '@testing-library/jest-dom';
import { render, screen } from '@testing-library/react';
import BitcoinStats from '../BitcoinStats';

jest.mock('../Prices', () => () => <div>Mocked Prices Component</div>);

describe('BitcoinStats', () => {
  it('renders the Prices component', () => {
    render(<BitcoinStats />);
    expect(screen.getByText('Mocked Prices Component')).toBeInTheDocument();
  });
});
