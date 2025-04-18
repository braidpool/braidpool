import React, { useState } from "react";
import {
  Dialog,
  DialogTitle,
  DialogContent,
  DialogActions,
  Button,
  Typography,
  Box,
  Tabs,
  Tab,
  Divider,
  Chip,
  Paper,
  styled,
  Stack,
} from "@mui/material";
import { BeadDisplayData } from "../../types/Bead";
import { mockBeads } from "../../data/mockBeads";

// Interface for component props
interface ShareDetailsProps {
  beadHash?: string;
  bead?: BeadDisplayData;
  open: boolean;
  onClose: () => void;
  onNavigateToBead?: (beadHash: string) => void;
}

// Styled components
const StyledPaper = styled(Paper)(({ theme }) => ({
  padding: theme.spacing(2),
  margin: theme.spacing(1, 0),
  borderRadius: theme.shape.borderRadius,
}));

const HashText = styled(Typography)(({ theme }) => ({
  fontFamily: "monospace",
  overflowWrap: "break-word",
}));

const LabelText = styled(Typography)(({ theme }) => ({
  fontWeight: "bold",
  color: theme.palette.text.secondary,
}));

const ValueText = styled(Typography)({
  wordBreak: "break-word",
});

// Tab panel component for tab content
interface TabPanelProps {
  children?: React.ReactNode;
  index: number;
  value: number;
}

function TabPanel(props: TabPanelProps) {
  const { children, value, index, ...other } = props;

  return (
    <div
      role="tabpanel"
      hidden={value !== index}
      id={`bead-tabpanel-${index}`}
      aria-labelledby={`bead-tab-${index}`}
      {...other}
    >
      {value === index && <Box sx={{ p: 3 }}>{children}</Box>}
    </div>
  );
}

/**
 * ShareDetails Component
 *
 * Displays detailed information about a bead/share in the Braidpool network.
 * Can be triggered from various places in the dashboard.
 */
export default function ShareDetails({
  beadHash,
  bead: propBead,
  open,
  onClose,
  onNavigateToBead,
}: ShareDetailsProps) {
  const [tabValue, setTabValue] = useState(0);

  // For demo purposes, if no bead is provided, use the tip bead from mock data
  // In production, this would fetch the bead data from an API
  const bead =
    propBead ||
    (beadHash
      ? Object.values(mockBeads).find((b) => b.beadHash === beadHash) ||
        mockBeads.tip
      : mockBeads.tip);

  // Handler for tab changes
  const handleTabChange = (event: React.SyntheticEvent, newValue: number) => {
    setTabValue(newValue);
  };

  // Handler for navigating to a parent bead
  const handleParentClick = (parentHash: string) => {
    if (onNavigateToBead) {
      onNavigateToBead(parentHash);
    }
    console.log("📣 Navigate to parent bead:", parentHash);
  };

  return (
    <Dialog
      open={open}
      onClose={onClose}
      maxWidth="md"
      fullWidth
      aria-labelledby="share-details-dialog-title"
    >
      <DialogTitle id="share-details-dialog-title">
        Share Details
        {bead.isTip && (
          <Chip size="small" label="Tip" color="secondary" sx={{ ml: 1 }} />
        )}
        {bead.isGenesis && (
          <Chip size="small" label="Genesis" color="primary" sx={{ ml: 1 }} />
        )}
      </DialogTitle>

      <DialogContent>
        {/* Bead Hash and Basic Info */}
        <StyledPaper elevation={1}>
          <Box sx={{ mb: 2 }}>
            <LabelText variant="subtitle2">Bead Hash</LabelText>
            <HashText variant="body2">{bead.beadHash}</HashText>
          </Box>

          <Stack
            spacing={2}
            direction={{ xs: "column", sm: "row" }}
            flexWrap="wrap"
          >
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Observation Time</LabelText>
              <ValueText variant="body2">{bead.formattedTimestamp}</ValueText>
            </Box>
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Cohort</LabelText>
              <ValueText variant="body2">{bead.cohortId}</ValueText>
            </Box>
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Validation Status</LabelText>
              <Chip
                size="small"
                label={bead.validationStatus}
                color={
                  bead.validationStatus === "valid"
                    ? "success"
                    : bead.validationStatus === "invalid"
                      ? "error"
                      : "warning"
                }
              />
            </Box>
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">
                Lesser Difficulty Target
              </LabelText>
              <ValueText variant="body2">
                {bead.lesserDifficultyTarget.toString(16)}
              </ValueText>
            </Box>
          </Stack>
        </StyledPaper>

        {/* Tabs for different sections */}
        <Box sx={{ borderBottom: 1, borderColor: "divider", mt: 2 }}>
          <Tabs
            value={tabValue}
            onChange={handleTabChange}
            aria-label="bead details tabs"
          >
            <Tab
              label="Block Header"
              id="bead-tab-0"
              aria-controls="bead-tabpanel-0"
            />
            <Tab
              label="Parents"
              id="bead-tab-1"
              aria-controls="bead-tabpanel-1"
            />
            <Tab
              label="Transactions"
              id="bead-tab-2"
              aria-controls="bead-tabpanel-2"
            />
          </Tabs>
        </Box>

        {/* Block Header Tab */}
        <TabPanel value={tabValue} index={0}>
          <Stack
            spacing={2}
            direction={{ xs: "column", sm: "row" }}
            flexWrap="wrap"
          >
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Version</LabelText>
              <ValueText variant="body2">{bead.blockHeader.version}</ValueText>
            </Box>
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Timestamp</LabelText>
              <ValueText variant="body2">
                {new Date(bead.blockHeader.timestamp).toLocaleString()}
              </ValueText>
            </Box>
            <Box sx={{ flex: "1 1 100%" }}>
              <LabelText variant="subtitle2">Previous Block Hash</LabelText>
              <HashText variant="body2">
                {bead.blockHeader.prevBlockHash}
              </HashText>
            </Box>
            <Box sx={{ flex: "1 1 100%" }}>
              <LabelText variant="subtitle2">Merkle Root</LabelText>
              <HashText variant="body2">{bead.blockHeader.merkleRoot}</HashText>
            </Box>
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Bits</LabelText>
              <ValueText variant="body2">{bead.blockHeader.bits}</ValueText>
            </Box>
            <Box sx={{ flex: "1 1 50%", minWidth: { xs: "100%", sm: "45%" } }}>
              <LabelText variant="subtitle2">Nonce</LabelText>
              <ValueText variant="body2">{bead.blockHeader.nonce}</ValueText>
            </Box>
          </Stack>
        </TabPanel>

        {/* Parents Tab */}
        <TabPanel value={tabValue} index={1}>
          {bead.parents.length === 0 ? (
            <Typography variant="body2">Genesis bead has no parents</Typography>
          ) : (
            bead.parents.map((parent, index) => (
              <StyledPaper key={index} elevation={1}>
                <Stack spacing={2}>
                  <Box>
                    <LabelText variant="subtitle2">Parent Hash</LabelText>
                    <Box display="flex" alignItems="center">
                      <HashText variant="body2">{parent.beadHash}</HashText>
                      <Button
                        size="small"
                        onClick={() => handleParentClick(parent.beadHash)}
                        sx={{ ml: 1 }}
                      >
                        View
                      </Button>
                    </Box>
                  </Box>
                  <Box>
                    <LabelText variant="subtitle2">Timestamp</LabelText>
                    <ValueText variant="body2">
                      {new Date(parent.timestamp).toLocaleString()}
                    </ValueText>
                  </Box>
                </Stack>
              </StyledPaper>
            ))
          )}
        </TabPanel>

        {/* Transactions Tab */}
        <TabPanel value={tabValue} index={2}>
          <Box sx={{ mb: 3 }}>
            <Typography variant="h6">Coinbase Transaction</Typography>
            <StyledPaper elevation={1}>
              <Stack spacing={2}>
                <Box>
                  <LabelText variant="subtitle2">Transaction ID</LabelText>
                  <HashText variant="body2">
                    {bead.coinbaseTransaction.transaction.txid}
                  </HashText>
                </Box>
                <Stack direction={{ xs: "column", sm: "row" }} spacing={2}>
                  <Box sx={{ flex: "1 1 50%" }}>
                    <LabelText variant="subtitle2">Version</LabelText>
                    <ValueText variant="body2">
                      {bead.coinbaseTransaction.transaction.version}
                    </ValueText>
                  </Box>
                  <Box sx={{ flex: "1 1 50%" }}>
                    <LabelText variant="subtitle2">Lock Time</LabelText>
                    <ValueText variant="body2">
                      {bead.coinbaseTransaction.transaction.lockTime}
                    </ValueText>
                  </Box>
                </Stack>
              </Stack>
            </StyledPaper>
          </Box>

          <Box sx={{ mb: 3 }}>
            <Typography variant="h6">Payout Update Transaction</Typography>
            <StyledPaper elevation={1}>
              <Stack spacing={2}>
                <Box>
                  <LabelText variant="subtitle2">Transaction ID</LabelText>
                  <HashText variant="body2">
                    {bead.payoutUpdateTransaction.transaction.txid}
                  </HashText>
                </Box>
                <Stack direction={{ xs: "column", sm: "row" }} spacing={2}>
                  <Box sx={{ flex: "1 1 50%" }}>
                    <LabelText variant="subtitle2">Version</LabelText>
                    <ValueText variant="body2">
                      {bead.payoutUpdateTransaction.transaction.version}
                    </ValueText>
                  </Box>
                  <Box sx={{ flex: "1 1 50%" }}>
                    <LabelText variant="subtitle2">Lock Time</LabelText>
                    <ValueText variant="body2">
                      {bead.payoutUpdateTransaction.transaction.lockTime}
                    </ValueText>
                  </Box>
                </Stack>
              </Stack>
            </StyledPaper>
          </Box>

          <Box>
            <Typography variant="h6">
              Other Transactions ({bead.transactions.length})
            </Typography>
            {bead.transactions.map((tx, index) => (
              <StyledPaper key={index} elevation={1}>
                <Stack spacing={2}>
                  <Box>
                    <LabelText variant="subtitle2">Transaction ID</LabelText>
                    <HashText variant="body2">{tx.txid}</HashText>
                  </Box>
                  <Stack direction={{ xs: "column", sm: "row" }} spacing={2}>
                    <Box sx={{ flex: "1 1 50%" }}>
                      <LabelText variant="subtitle2">Size</LabelText>
                      <ValueText variant="body2">{tx.size} bytes</ValueText>
                    </Box>
                    <Box sx={{ flex: "1 1 50%" }}>
                      <LabelText variant="subtitle2">Weight</LabelText>
                      <ValueText variant="body2">{tx.weight}</ValueText>
                    </Box>
                  </Stack>
                </Stack>
              </StyledPaper>
            ))}
          </Box>
        </TabPanel>
      </DialogContent>

      <DialogActions>
        <Button onClick={onClose}>Close</Button>
      </DialogActions>
    </Dialog>
  );
}
