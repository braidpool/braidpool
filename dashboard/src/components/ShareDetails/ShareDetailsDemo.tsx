import React, { useState } from 'react';
import { Button, Box, Typography, Paper, styled } from '@mui/material';
import ShareDetails from './ShareDetails';
import { mockBeads, printDebug } from '../../data/mockBeads';

// Styled components
const StyledPaper = styled(Paper)(({ theme }) => ({
  padding: theme.spacing(3),
  margin: theme.spacing(2),
  display: 'flex',
  flexDirection: 'column',
  gap: theme.spacing(2),
}));

/**
 * ShareDetailsDemo Component
 *
 * A simple demo component that shows how to use the ShareDetails component.
 * It provides buttons to open different types of beads in the ShareDetails modal.
 */
export default function ShareDetailsDemo() {
  const [open, setOpen] = useState(false);
  const [selectedBead, setSelectedBead] = useState<string | null>(null);

  // Handler for opening the modal with a specific bead
  const handleOpenBead = (beadType: string) => {
    setSelectedBead(beadType);
    setOpen(true);
    console.log('🔍 Opening bead details for:', beadType);
    printDebug(); // Print debug information to console
  };

  // Handler for closing the modal
  const handleClose = () => {
    setOpen(false);
  };

  // Handler for navigating to a different bead
  const handleNavigateToBead = (beadHash: string) => {
    const beadType = Object.entries(mockBeads).find(
      ([_, bead]) => bead.beadHash === beadHash
    )?.[0];

    if (beadType) {
      setSelectedBead(beadType);
      console.log('🔄 Navigating to bead:', beadType);
    }
  };

  return (
    <Box>
      <Typography variant="h4" gutterBottom>
        Share Details Component Demo
      </Typography>

      <StyledPaper elevation={3}>
        <Typography variant="h6">
          Open different types of beads to see the ShareDetails component in
          action
        </Typography>

        <Box display="flex" gap={2}>
          <Button
            variant="contained"
            color="primary"
            onClick={() => handleOpenBead('genesis')}
          >
            Open Genesis Bead
          </Button>

          <Button
            variant="contained"
            color="secondary"
            onClick={() => handleOpenBead('regular')}
          >
            Open Regular Bead
          </Button>

          <Button
            variant="contained"
            color="info"
            onClick={() => handleOpenBead('tip')}
          >
            Open Tip Bead
          </Button>
        </Box>

        <Typography variant="body2" color="textSecondary">
          Click "View" on parent beads to navigate between related beads.
        </Typography>
      </StyledPaper>

      {/* The ShareDetails component */}
      <ShareDetails
        open={open}
        onClose={handleClose}
        bead={selectedBead ? mockBeads[selectedBead] : undefined}
        onNavigateToBead={handleNavigateToBead}
      />
    </Box>
  );
}
