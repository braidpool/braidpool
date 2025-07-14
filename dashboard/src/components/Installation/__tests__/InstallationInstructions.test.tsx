import { render, screen } from '@testing-library/react';
import '@testing-library/jest-dom';
import InstallationInstructions from '../InstallationInstructions';

// Mocking the Card component
jest.mock(
  '../../common/Card',
  () =>
    ({ title, subtitle, accentColor, children }: any) => (
      <div data-testid="card">
        <h2>{title}</h2>
        <h3>{subtitle}</h3>
        {children}
      </div>
    )
);

jest.mock('@mui/icons-material', () => ({
  ArrowForward: () => <div data-testid="ArrowForwardIcon" />,
  CloudDownload: () => <div data-testid="CloudDownloadIcon" />,
  Terminal: () => <div data-testid="TerminalIcon" />,
  PlayCircleOutline: () => <div data-testid="PlayCircleOutlineIcon" />,
  Code: () => <div data-testid="CodeIcon" />,
}));
describe('InstallationInstructions', () => {
  it('renders InstallationInstructions with headings and instructions', () => {
    render(<InstallationInstructions />);

    // Check Card title and subtitle
    expect(screen.getByText('Installation Instructions')).toBeInTheDocument();
    expect(
      screen.getByText('How to install and set up Braidpool')
    ).toBeInTheDocument();

    // Check section headers
    expect(screen.getByText('Basic Installation')).toBeInTheDocument();
    expect(screen.getByText('CPUnet Testing Node')).toBeInTheDocument();

    // Check that View Full Documentation button exists
    expect(
      screen.getByRole('button', { name: /view full documentation/i })
    ).toBeInTheDocument();
  });
});
