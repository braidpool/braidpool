import React, { ReactNode } from 'react';
import { IconButton, SxProps, Theme } from '@mui/material';

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
      size='small'
      onClick={onClick}
      sx={{
        color: '#7f7f7f',
        bgcolor: '#f2f2f2',
        p: 1,
        width: 34,
        height: 34,
        boxShadow: '0 1px 2px rgba(0,0,0,0.05)',
        '&:hover': {
          bgcolor: '#e6e6e6',
          boxShadow: '0 1px 3px rgba(0,0,0,0.1)',
        },
        ...sx,
      }}>
      {icon}
    </IconButton>
  );
};

export default ActionIconButton;
