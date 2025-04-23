import React, { ReactNode, ReactElement } from 'react';

interface ActionIconButtonProps {
  icon: ReactElement;
  onClick?: () => void;
  className?: string;
}
const ActionIconButton: React.FC<ActionIconButtonProps> = ({
  icon,
  onClick,
  className = '',
}) => {
  return (
    <button
      onClick={onClick}
      className={`w-[34px] h-[34px] p-1 text-white bg-[#36454F] shadow-sm hover:bg-black hover:shadow-md rounded-full ${className}`}
    >
      {React.cloneElement(icon, { className: 'text-inherit' })}
    </button>
  );
};

export default ActionIconButton;
