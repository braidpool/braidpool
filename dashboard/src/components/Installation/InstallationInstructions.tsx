import Card from '../common/Card';
import colors from '../../theme/colors';
import PlayCircleOutlineIcon from '@mui/icons-material/PlayCircleOutline';
import CodeIcon from '@mui/icons-material/Code';
import CloudDownloadIcon from '@mui/icons-material/CloudDownload';
import TerminalIcon from '@mui/icons-material/Terminal';
import ArrowForwardIcon from '@mui/icons-material/ArrowForward';

const InstallationInstructions = () => {
  return (
    <Card
      title="Installation Instructions"
      subtitle="How to install and set up Braidpool"
      accentColor={colors.cardAccentPrimary}
    >
      <div className="flex-col gap-12">
        <div className="flex-1">
          <div
            className="p-4 rounded h-full"
            style={{
              backgroundColor: colors.paper,
              border: `1px solid ${colors.primary}20`,
            }}
          >
            <h6 className="mb-4 font-medium text-lg">Basic Installation</h6>
            <p className="mb-6 text-sm" style={{ color: colors.textSecondary }}>
              Follow these steps to install and run Braidpool node on your
              system. Make sure you have the prerequisites installed before
              proceeding.
            </p>

            <ul className="pl-0">
              {[
                {
                  icon: <CloudDownloadIcon fontSize="small" />,
                  primary: 'Clone the repository',
                  secondary:
                    'git clone https://github.com/braidpool/braidpool.git',
                },
                {
                  icon: <TerminalIcon fontSize="small" />,
                  primary: 'Build the node',
                  secondary: 'cd node && cargo build',
                },
                {
                  icon: <PlayCircleOutlineIcon fontSize="small" />,
                  primary: 'Run the first seed node',
                  secondary:
                    'cargo run -- --bind=localhost:8989 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332',
                },
              ].map((item, index) => (
                <li key={index} className="px-0 py-1">
                  <div className="flex items-start">
                    <div
                      className="min-w-[36px] pt-1"
                      style={{ color: colors.primary }}
                    >
                      {item.icon}
                    </div>
                    <div className="flex-1">
                      <p
                        className="text-sm font-medium mb-1"
                        style={{ color: colors.textPrimary }}
                      >
                        {item.primary}
                      </p>
                      <div
                        className="text-xs bg-black/10 px-2 py-1 rounded font-mono overflow-x-auto"
                        style={{ color: colors.textSecondary }}
                      >
                        {item.secondary}
                      </div>
                    </div>
                  </div>
                </li>
              ))}
            </ul>

            <div className="mt-6 flex justify-center">
              <button
                className="flex items-center gap-2 px-4 py-2 rounded normal-case"
                style={{
                  backgroundColor: colors.primary,
                  color: 'white',
                }}
                onClick={() => console.log('📝 Opening full documentation...')}
              >
                <CodeIcon fontSize="small" />
                View Full Documentation
              </button>
            </div>
          </div>
        </div>

        <div className="flex-1">
          <div
            className="p-4 rounded h-full"
            style={{
              backgroundColor: colors.paper,
              border: `1px solid ${colors.primary}20`,
            }}
          >
            <h6 className="mb-4 font-medium text-lg">CPUnet Testing Node</h6>
            <p className="mb-6 text-sm" style={{ color: colors.textSecondary }}>
              For testing purposes, you can set up the CPUnet testing node using
              nix-script from the root directory.
            </p>

            <ul className="pl-0">
              {[
                {
                  icon: <TerminalIcon fontSize="small" />,
                  primary: 'Build the nix-script',
                  secondary: 'nix-build cpunet_node.nix',
                },
                {
                  icon: <ArrowForwardIcon fontSize="small" />,
                  primary: 'Navigate to result directory',
                  secondary: 'cd result',
                },
                {
                  icon: <PlayCircleOutlineIcon fontSize="small" />,
                  primary: 'Run the CPUnet node',
                  secondary:
                    './bin/bitcoind -cpunet -zmqpubsequence=tcp://127.0.0.1:28338',
                },
                {
                  icon: <TerminalIcon fontSize="small" />,
                  primary: 'Generate blocks',
                  secondary:
                    "./contrib/cpunet/miner --cli=./bin/bitcoin-cli --ongoing --address `./bin/bitcoin-cli -cpunet getnewaddress` --grind-cmd='./bin/bitcoin-util -cpunet -ntasks=1 grind'",
                },
              ].map((item, index) => (
                <li key={index} className="px-0 py-1">
                  <div className="flex items-start">
                    <div
                      className="min-w-[36px] pt-1"
                      style={{ color: colors.primary }}
                    >
                      {item.icon}
                    </div>
                    <div className="flex-1">
                      <p
                        className="text-sm font-medium mb-1"
                        style={{ color: colors.textPrimary }}
                      >
                        {item.primary}
                      </p>
                      <div
                        className="text-xs bg-black/10 px-2 py-1 rounded font-mono overflow-x-auto"
                        style={{ color: colors.textSecondary }}
                      >
                        {item.secondary}
                      </div>
                    </div>
                  </div>
                </li>
              ))}
            </ul>

            <hr className="my-4" style={{ borderColor: colors.primary }} />

            <h6 className="mb-2 font-medium text-sm">Prerequisites</h6>
            <ul className="list-disc pl-4 space-y-1">
              {[
                'Rust toolchain (rustc, cargo)',
                'Nix package manager (for CPUnet)',
                'Bitcoin Core (for RPC and ZMQ access)',
              ].map((item, index) => (
                <li
                  key={index}
                  className="text-xs"
                  style={{ color: colors.textSecondary }}
                >
                  {item}
                </li>
              ))}
            </ul>
          </div>
        </div>
      </div>
    </Card>
  );
};

export default InstallationInstructions;
