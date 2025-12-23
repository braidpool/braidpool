import React, { useEffect, useState } from 'react';
import RecentBlocksTable from './RecentBlocksTable';
import colors from '../../theme/colors';
import { Block } from './Types';
import { fetchPreviousBlocks } from './Utils';
import BlockInfoDialog from './BlockDialog';
import { WEBSOCKET_URLS } from '../../URLs';

const BlockViewer: React.FC = () => {
  const [nextBlock, setNextBlock] = useState<Block | null>(null);
  const [previousBlocks, setPreviousBlocks] = useState<Block[]>([]);
  const [isConnected, setIsConnected] = useState(false);
  const [isLoading, setIsLoading] = useState(true);
  const [selectedBlock, setSelectedBlock] = useState<string | null>(null);

  useEffect(() => {
    const getBlocks = async () => {
      setIsLoading(true);
      try {
        const data = await fetchPreviousBlocks();
        setPreviousBlocks(data);
      } catch (err) {
        console.log('Could not load blocks');
      } finally {
        setIsLoading(false);
      }
    };

    getBlocks();
  }, []);

  // Setup WebSocket for next block updates via mempool API - Note - it shows 8080but works as backend for API's websocket
  useEffect(() => {
    const socket = new WebSocket(WEBSOCKET_URLS.BLOCK_VIEWER_WEBSOCKET);

    socket.onopen = () => {
      setIsConnected(true);
      socket.send(
        JSON.stringify({
          action: 'want',
          data: ['blocks'],
        })
      );
    };

    socket.onmessage = (event: MessageEvent) => {
      try {
        const data = JSON.parse(event.data);

        if (data.block) {
          setNextBlock(data.block);
          // Add to previous blocks if not already there
          setPreviousBlocks((prev) => {
            const exists = prev.some((b) => b.id === data.block.id);
            if (!exists) {
              return [data.block, ...prev.slice(0, 14)]; // Keep only 15 blocks
            }
            return prev;
          });
        }
      } catch (err) {
        console.error('Failed to parse WS message', err);
      }
    };

    socket.onerror = (err) => {
      console.error('WebSocket error:', err);
      setIsConnected(false);
    };

    socket.onclose = () => {
      setIsConnected(false);
      console.log('WebSocket disconnected');
    };

    return () => {
      if (socket.readyState === WebSocket.OPEN) {
        socket.close();
      }
    };
  }, []);

  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-64 p-4">
        <div className="text-white">Loading blocks...</div>
      </div>
    );
  }

  // Combine next block with previous blocks and avoid duplicates
  const allBlocks = nextBlock
    ? [nextBlock, ...previousBlocks.filter((b) => b.id !== nextBlock.id)]
    : previousBlocks;

  if (allBlocks.length === 0) {
    return (
      <div className="flex items-center justify-center h-50 p-4">
        <div className="text-white">No blocks available</div>
      </div>
    );
  }

  // Calculate maximum block size for relative sizing
  const maxBlockSize = Math.max(...allBlocks.map((block) => block.size), 1);

  return (
    <div className="max-w-screen w-full overflow-x-hidden">
      <div className="p-4">
        <h2 className="text-white text-xl font-bold mb-4">Block Explorer</h2>
        <div
          className="flex items-end gap-4 overflow-x-auto pb-4"
          style={{
            scrollbarWidth: 'thin',
            scrollbarColor: `${colors.primary} ${colors.paper}`,
          }}
        >
          {allBlocks.map((block, idx) => {
            const feeRange = block.extras?.feeRange?.map((fee) =>
              Math.round(fee)
            );
            const minFee = feeRange ? Math.min(...feeRange) : 0;
            const maxFee = feeRange ? Math.max(...feeRange) : 0;
            const blockHeightPercent = Math.min(
              100,
              (block.size / maxBlockSize) * 100
            );

            return (
              <div
                key={block.id}
                className="flex flex-col items-center min-w-[180px]"
              >
                {/* Highlight the next block */}
                {idx === 0 && nextBlock && (
                  <div className="text-green-400 text-xs mb-1">Next</div>
                )}

                {/* Block visualization */}
                <div
                  className={`w-full rounded-t-md ${idx === 0 ? 'bg-green-500' : 'bg-blue-500'} relative overflow-hidden transition-all duration-300`}
                  style={{
                    height: `${blockHeightPercent}%`,
                    minHeight: '80px',
                  }}
                  onClick={() => setSelectedBlock(block.id)}
                >
                  <div className="absolute bottom-0 left-0 right-0 p-2 bg-black bg-opacity-50">
                    <div className="text-white text-center font-bold">
                      {(block.extras?.reward / 100000000).toFixed(2) || 0} BTC
                    </div>
                    <div className="text-white text-center text-sm">
                      {block.tx_count.toLocaleString()} txs
                    </div>
                  </div>
                </div>

                {/* Block footer */}
                <div className="w-full bg-gray-800 rounded-b-md p-3">
                  <div className="text-white text-center text-sm">
                    Height: {block.height}
                  </div>
                  <div className="text-yellow-400 text-center text-xs">
                    {minFee} - {maxFee} sat/vB
                  </div>
                  <div className="text-gray-400 text-center text-xs mt-1">
                    ~{Math.round(block.extras?.medianFee) || 0} sat/vB median
                  </div>
                </div>
              </div>
            );
          })}
        </div>

        <div className="text-gray-500 text-xs mt-2">
          {isConnected ? (
            <span className="text-green-400">●</span>
          ) : (
            <span className="text-red-400">●</span>
          )}{' '}
          {isConnected ? 'Connected' : 'Disconnected'}
        </div>
      </div>
      {selectedBlock && (
        <BlockInfoDialog
          hash={selectedBlock}
          onClose={() => setSelectedBlock(null)}
        />
      )}
      <RecentBlocksTable blocks={allBlocks} />
    </div>
  );
};

export default BlockViewer;
