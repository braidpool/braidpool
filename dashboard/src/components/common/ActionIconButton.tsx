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
      className={`
        w-[34px] h-[34px] p-1 text-white bg-[#36454F]
        shadow-sm hover:bg-black hover:shadow-md rounded-full
        sm:w-[34px] sm:h-[34px]    
        xs:w-[28px] xs:h-[28px]    
        ${className}
      `}
    >
      {React.cloneElement(icon, { className: 'text-inherit w-full h-full' })}
    </button>
  );
};

export default ActionIconButton;
