import '@testing-library/jest-dom';
import { render, screen } from '@testing-library/react';
import Footer from '../Footer';
import { EXTERNAL_LINKS } from '../../../URLs';

describe('Footer Component', () => {
  let consoleErrorSpy: jest.SpyInstance;

  beforeEach(() => {
    jest.clearAllMocks();
    consoleErrorSpy = jest.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    consoleErrorSpy.mockRestore();
  });

  it('renders project links with correct URLs', () => {
    render(<Footer />);

    expect(screen.getByText('About')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.ABOUT
    );
    expect(screen.getByText('Documentation')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.DOCUMENTATION
    );
    expect(screen.getByText('Contribute')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.CONTRIBUTE
    );
  });

  it('renders community links with correct URLs', () => {
    render(<Footer />);

    expect(screen.getByText('GitHub')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.GITHUB
    );
    expect(screen.getByText('Twitter')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.TWITTER
    );
    expect(screen.getByText('Discord')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.DISCORD
    );
  });

  it('renders legal links with correct URLs', () => {
    render(<Footer />);

    expect(screen.getByText('APGL-3.0 License')).toHaveAttribute(
      'href',
      EXTERNAL_LINKS.LICENSE
    );
  });

  it('renders without any console errors', () => {
    render(<Footer />);
    expect(consoleErrorSpy).not.toHaveBeenCalled();
  });
});
