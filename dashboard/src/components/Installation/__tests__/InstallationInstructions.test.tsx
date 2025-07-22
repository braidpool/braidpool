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

// Mock react-icons/md
jest.mock('react-icons/md', () => ({
  MdArrowForward: () => <div data-testid="MdArrowForwardIcon" />,
  MdCloudDownload: () => <div data-testid="MdCloudDownloadIcon" />,
  MdTerminal: () => <div data-testid="MdTerminalIcon" />,
  MdPlayCircleOutline: () => <div data-testid="MdPlayCircleOutlineIcon" />,
  MdCode: () => <div data-testid="MdCodeIcon" />,
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

    // Check icons
    expect(screen.getAllByTestId(/Md.*Icon/).length).toBeGreaterThan(0);
  });
});
