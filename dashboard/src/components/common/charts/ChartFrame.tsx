import { useRef } from 'react';
import { Download } from 'lucide-react';
import { downloadSvgFromContainer } from '../../../utils/downloadSvg';
import type { ChartFrameProps } from './Type';

const ChartFrame = ({
  children,
  title,
  description,
  headerRight,
  downloadFileName = 'chart',
  className = '',
  height = 350,
}: ChartFrameProps) => {
  const containerRef = useRef<HTMLDivElement | null>(null);

  const handleDownload = () => {
    if (containerRef.current) {
      downloadSvgFromContainer(containerRef.current, downloadFileName);
    }
  };

  return (
    <section
      className={`relative border border-gray-800/50 rounded-xl p-4 w-full backdrop-blur-md overflow-hidden ${className}`}
      style={{ minHeight: title ? height + 48 : height }}
    >
      {title && (
        <header className="flex items-start justify-between mb-4">
          <div>
            <div className="flex items-center gap-2">
              <h3 className="text-xl font-bold text-blue-300">{title}</h3>
              <button
                type="button"
                onClick={handleDownload}
                className="p-1.5 rounded text-gray-500 hover:text-gray-300 hover:bg-gray-800 transition-colors"
                aria-label="Download chart"
              >
                <Download className="w-4 h-4" />
              </button>
            </div>
            {description && (
              <div className="text-sm text-gray-400 mt-1">{description}</div>
            )}
          </div>
          {headerRight}
        </header>
      )}
      <div ref={containerRef} style={{ width: '100%', height }}>
        {children}
      </div>
    </section>
  );
};

export default ChartFrame;
