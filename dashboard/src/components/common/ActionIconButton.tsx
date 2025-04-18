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
        color: '#000',
        bgcolor: colors.accent,
        p: 1,
        width: 34,
        height: 34,
        boxShadow: '0 1px 2px rgba(0,0,0,0.3)',
        '&:hover': {
          bgcolor: colors.accentDark,
          boxShadow: '0 2px 4px rgba(0,0,0,0.3)',
        },
        ...sx,
      }}
    >
      {icon}
    </IconButton>
  );
};

export default ActionIconButton;
