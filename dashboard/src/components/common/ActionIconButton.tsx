import React, { ReactNode } from 'react';
import { IconButton, SxProps, Theme } from '@mui/material';
import colors from '../../theme/colors';

interface ActionIconButtonProps {
  icon: ReactNode;
  onClick?: () => void;
  sx?: SxProps<Theme>;
}

/**
 * A consistent button style used in the header and throughout the app
 */
const ActionIconButton: React.FC<ActionIconButtonProps> = ({
  icon,
  onClick,
  sx = {},
}) => {
  return (
    <IconButton
    size="small"
    onClick={onClick}
    sx={{
      color: 'white',
      background: '#36454F',
      p: 1,
      width: 34,
      height: 34,
      boxShadow: '0 1px 2px rgba(0,0,0,0.3)',
      '&:hover': {
        background: '#000',
        boxShadow: '0 2px 4px rgba(0,0,0,0.4)',
      },
      ...sx,
    }}
  >
    {React.cloneElement(icon, { style: { color: 'inherit' } })}
  </IconButton>
  

  );
};

export default ActionIconButton;
