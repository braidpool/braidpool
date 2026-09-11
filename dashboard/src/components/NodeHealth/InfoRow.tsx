export const InfoRow = ({
  label,
  value,
  mono = false,
}: {
  label: string;
  value: string | number;
  mono?: boolean;
}) => (
  <div className="flex justify-between items-baseline gap-4">
    <span className="text-gray-500 shrink-0">{label}</span>
    <span
      className={`font-medium text-white text-right ${mono ? 'font-mono' : ''}`}
    >
      {value}
    </span>
  </div>
);
