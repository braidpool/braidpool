import { useState, useMemo } from 'react';
import { PeerInfo } from './Types';
import { formatBytes, paginate, calculateTotalPages } from './Utils';
import { ITEMS_PER_PAGE } from './Constants';

export default function Peers({ peers }: { peers: PeerInfo[] }) {
  const [currentPage, setCurrentPage] = useState(1);
  const totalPages = useMemo(
    () => calculateTotalPages(peers.length, ITEMS_PER_PAGE),
    [peers.length]
  );

  const paginatedPeers = paginate(peers, currentPage, ITEMS_PER_PAGE);
  const handlePrev = () => {
    setCurrentPage((prev) => Math.max(prev - 1, 1));
  };

  const handleNext = () => {
    setCurrentPage((prev) => Math.min(prev + 1, totalPages));
  };

  return (
    <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md">
      <div className="px-6 py-4 border-b border-gray-700">
        <h2 className="text-white text-xl font-semibold">Connected Peers</h2>
        <p className="text-gray-300 text-sm">
          {peers.length} total peers connected
        </p>
      </div>

      <div className="px-6 py-4 space-y-4 max-sm:h-[1116px] md:h-[648px] ">
        {paginatedPeers.map((peer) => (
          <div
            key={peer.id}
            className="flex max-sm:flex-col md:flex-row md:items-start md:justify-between gap-4 p-4 border border-gray-700 rounded-lg bg-gray-900/30 hover:bg-gray-900/50 transition-colors overflow-x-hidden"
          >
            <div className="flex-1 space-y-1 min-w-0">
              <p className="text-white font-medium">{peer.addr}</p>

              <div
                className={`text-sm w-fit px-2 py-0.5 rounded-full font-medium ${
                  peer.inbound
                    ? 'text-white bg-blue-600'
                    : 'text-gray-200 bg-gray-600'
                }`}
              >
                {peer.inbound ? 'Inbound' : 'Outbound'}
              </div>

              <div className="flex max-sm:flex-col md:flex-row lg:gap-1">
                <p className="text-sm text-gray-400">Version:</p>
                <p className="text-sm text-white break-words">{peer.subver}</p>
              </div>
            </div>

            <div className="flex flex-col max-sm:w-full max-sm:pt-2 md:text-right gap-1">
              <p className="text-sm text-gray-400">
                Ping:{' '}
                <span className="text-white font-mono">{peer.pingtime}ms</span>
              </p>
              <p className="text-sm text-gray-400">
                ↑ {formatBytes(peer.bytessent)} ↓ {formatBytes(peer.bytesrecv)}
              </p>
            </div>
          </div>
        ))}

        {[...Array(ITEMS_PER_PAGE - paginatedPeers.length)].map((_, idx) => (
          <div
            key={`empty-${idx}`}
            className="grid md:grid-cols-2 p-4 border border-transparent rounded-lg h-[96px]"
          />
        ))}
      </div>

      {/* Pagination Controls */}
      <div className="px-6 py-4 flex justify-between items-center border-t border-gray-700 text-sm text-gray-300">
        <button
          onClick={handlePrev}
          disabled={currentPage === 1}
          className={`px-3 py-1 rounded ${
            currentPage === 1
              ? 'opacity-50 cursor-not-allowed'
              : 'hover:bg-gray-800'
          }`}
        >
          Previous
        </button>

        <span>
          Page {currentPage} of {totalPages}
        </span>

        <button
          onClick={handleNext}
          disabled={currentPage === totalPages}
          className={`px-3 py-1 rounded ${
            currentPage === totalPages
              ? 'opacity-50 cursor-not-allowed'
              : 'hover:bg-gray-800'
          }`}
        >
          Next
        </button>
      </div>
    </div>
  );
}
