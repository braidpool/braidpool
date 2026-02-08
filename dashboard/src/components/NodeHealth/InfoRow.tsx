export const InfoRow = ({
  label,
  value,
}: {
  label: string;
  value: string | number;
}) => (
  <div className="flex justify-between">
    <span className="text-textSecondary">{label}</span>
    <span className="font-medium text-textPrimary">{value}</span>
  </div>
);
