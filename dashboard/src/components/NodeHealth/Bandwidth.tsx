import { Wifi } from 'lucide-react';
import RawJsonViewer from './Rawdatajson';
import { NetTotals } from './__tests__/types';
import { formatBytes } from './__tests__/utils';
import { formatDuration } from './__tests__/utils';

export default function BandwidthPanel({
  nettotals,
}: {
  nettotals: NetTotals;
}) {
  return (
    <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
      {/* Traffic Card */}
      <div className="bg-[#1c1c1c] border border-gray-700 rounded-lg p-6 backdrop-blur-sm">
        <div className="mb-4">
          <h2 className="text-xl font-semibold text-white">Network Traffic</h2>
        </div>

        <div className="grid grid-cols-2 gap-4 mb-4">
          <div className="text-center p-4 border border-gray-700 rounded-lg bg-gray-900/30">
            <Wifi className="w-8 h-8 mx-auto mb-2 text-blue-400" />
            <p className="text-sm font-medium text-gray-300">Total Received</p>
            <p className="text-lg font-bold text-white">
              {formatBytes(nettotals.totalbytesrecv)}
            </p>
          </div>
          <div className="text-center p-4 border border-gray-700 rounded-lg bg-gray-900/30">
            <Wifi className="w-8 h-8 mx-auto mb-2 text-green-400" />
            <p className="text-sm font-medium text-gray-300">Total Sent</p>
            <p className="text-lg font-bold text-white">
              {formatBytes(nettotals.totalbytessent)}
            </p>
          </div>
        </div>

        <div>
          <p className="text-sm font-medium text-gray-300 mb-2">
            Upload Target
          </p>
          <div className="space-y-2">
            <div className="flex justify-between text-sm">
              <span className="text-gray-300">Bytes left in cycle</span>
              <span className="text-white">
                {formatBytes(nettotals.uploadtarget.bytes_left_in_cycle)}
              </span>
            </div>
            <div className="flex justify-between text-sm">
              <span className="text-gray-300">Time left in cycle</span>
              <span className="text-white">
                {formatDuration(
                  nettotals.uploadtarget.time_left_in_cycle * 1000
                )}
              </span>
            </div>
          </div>
        </div>
      </div>

      <RawJsonViewer data={nettotals} />
    </div>
  );
}
