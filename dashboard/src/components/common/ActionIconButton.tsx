import React, { ReactNode, ReactElement } from 'react';

interface ActionIconButtonProps {
  icon: React.ReactElement<any>;
  onClick?: () => void;
  className?: string;
  ariaLabel: string;
}
const ActionIconButton: React.FC<ActionIconButtonProps> = ({
  icon,
  onClick,
  className = '',
  ariaLabel,
}) => {
  return (
    <button
      type="button"
      onClick={onClick}
      aria-label={ariaLabel}
      className={`
        flex items-center justify-center
        w-[34px] h-[34px] sm:w-[34px] sm:h-[34px] xs:w-[28px] xs:h-[28px]
        p-1 rounded-full bg-[#36454F] text-white
        shadow-md hover:shadow-lg hover:bg-black
        focus:outline-none focus:ring-2 focus:ring-white/70 focus:ring-offset-1
        ${className}
      `}
    >
      {React.cloneElement(icon, {
        className: 'w-[18px] h-[18px] text-inherit',
      })}
    </button>
  );
};

export default ActionIconButton;
