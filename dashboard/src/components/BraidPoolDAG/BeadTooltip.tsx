import React from 'react';
import { BeadTooltipProps } from './Types';
import { MAX_TOOLTIP_CHILDREN } from './Constants';
import { shortenHash } from '../BeadsTab/lib/Utils';

const HashList: React.FC<{ hashes: string[]; arrowClass: string }> = ({
  hashes,
  arrowClass,
}) => (
  <div className="mt-1 pl-2">
    {hashes.map((hash) => (
      <div key={hash} className="my-0.5 text-[10px]">
        <span className={arrowClass}>→</span>{' '}
        <span className="font-mono text-[#48CAE4]">
          {shortenHash(hash, 12, 8)}
        </span>
      </div>
    ))}
  </div>
);

const BeadTooltip: React.FC<BeadTooltipProps> = ({
  bead,
  cohortIndex,
  hwpPosition,
}) => {
  const hiddenChildren = bead.children.length - MAX_TOOLTIP_CHILDREN;

  return (
    <div className="max-w-[400px] text-xs leading-relaxed">
      <div className="mb-2 pb-2">
        <strong>Bead Information</strong>
      </div>
      <div className="mb-1 break-all">
        <strong>Hash:</strong>{' '}
        <span className="font-mono text-[10px]">{bead.id}</span>
      </div>
      <div className="mb-1">
        <strong>Cohort Index:</strong> {cohortIndex ?? 'N/A'}
      </div>
      <div className="mb-1">
        <strong>On HWP:</strong>{' '}
        <span className={hwpPosition ? 'text-green-400' : 'text-red-500'}>
          {hwpPosition ? `Yes (Position: ${hwpPosition})` : 'No'}
        </span>
      </div>

      <div className="mt-2 pt-2 border-t border-[#48CAE4]">
        <strong>Parents ({bead.parents.length}):</strong>
        {bead.parents.length > 0 ? (
          <HashList hashes={bead.parents} arrowClass="text-[#FF8500]" />
        ) : (
          <span className="text-[#999]"> None (Genesis)</span>
        )}
      </div>

      <div className="mt-2 pt-2 border-t border-[#48CAE4]">
        <strong>Children ({bead.children.length}):</strong>
        {bead.children.length > 0 ? (
          <>
            <HashList
              hashes={bead.children.slice(0, MAX_TOOLTIP_CHILDREN)}
              arrowClass="text-green-400"
            />
            {hiddenChildren > 0 && (
              <div className="mt-0.5 pl-2 text-[10px] text-[#999]">
                ... and {hiddenChildren} more
              </div>
            )}
          </>
        ) : (
          <span className="text-[#999]"> None (Leaf bead)</span>
        )}
      </div>
    </div>
  );
};

export default BeadTooltip;
