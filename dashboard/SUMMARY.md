# BraidPool Dashboard Summary

## Overview
BraidPool Dashboard is a sophisticated real-time web application for monitoring and visualizing a Bitcoin mining pool. It provides live updates on mining operations, block discovery, network statistics, and pool performance through an intuitive dark-themed interface.

## Technology Stack

### Frontend
- **React 19.1.0** with TypeScript for component-based UI
- **Vite** for fast development and optimized builds
- **Material-UI v7** for polished UI components
- **TailwindCSS v4** for utility styling
- **D3.js** for complex DAG visualizations
- **Recharts** for standard charts
- **React Router v7** for navigation

### Backend
- **Node.js** with ES modules
- **WebSocket (ws)** for real-time data streaming
- **Express.js** for HTTP server setup
- **Bitcoin RPC** integration for blockchain data
- **External APIs** for price and market data

## Architecture

### Frontend Structure
```
src/
├── components/           # UI components organized by feature
│   ├── Dashboard/       # Main dashboard views
│   ├── BeadsTab/       # Block explorer and rewards
│   ├── BraidPoolDAG/   # DAG visualization
│   ├── BitcoinStats/   # Network statistics
│   └── common/         # Shared components
├── types/              # TypeScript definitions
├── utils/              # Helper functions
└── theme/              # UI theming
```

### Backend Structure
```
api/
├── server.js           # WebSocket server (port 5000)
├── ws/                 # WebSocket message handlers
└── utils/              # Data fetching utilities
```

## Key Features

### 1. Real-Time Dashboard
- Live pool hashrate monitoring
- Active mempool transaction tracking
- Recent blocks table with detailed information
- Network difficulty and mining statistics

### 2. Beads Explorer
- Real-time block discovery visualization
- Expandable block details showing:
  - Block hash and height
  - Timestamp and work value
  - Transaction count and fees
  - Mining rewards distribution
- Transaction-level detail views
- Trends analysis for hashrate, latency, and transactions

### 3. DAG Visualization
- Interactive directed acyclic graph of the BraidPool
- Visual representation of block relationships
- Zoom, pan, and node interaction capabilities
- Real-time updates as new blocks are discovered

### 4. Mining Inventory
- Hardware monitoring dashboard
- Connected miner status tracking
- Performance metrics per device

### 5. Network Statistics
- Bitcoin price tracking
- Global cryptocurrency market data
- Network hashrate and difficulty charts
- Mempool congestion analysis

## Data Flow

### WebSocket Communication
The application uses WebSocket for all real-time data:

1. **Client connects** to ws://localhost:5000
2. **Server broadcasts** updates every 10 seconds:
   - `bitcoin_update` - Price and market data
   - `block_data` - New block information
   - `hashrate_data` - Network hashrate
   - `latency_data` - Network latency
   - `reward_data` - Mining rewards

3. **RPC Calls** - Clients can request specific data via WebSocket RPC

### Data Sources
- **Blockchain Data**: Bitcoin Core RPC
- **Market Data**: External cryptocurrency APIs
- **Pool Data**: BraidPool simulator API (port 65433)
- **Network Stats**: Aggregated from multiple sources

## Security Features

1. **RPC Whitelist**: Only approved RPC methods allowed
2. **Input Validation**: All WebSocket messages validated
3. **CORS Configuration**: Controlled cross-origin access
4. **Environment Variables**: Sensitive data in .env files

## Component Organization

### Shared Components (`src/components/common/`)
- `Card.tsx` - Reusable card container
- `Header.tsx` - App header with navigation
- `KPICard.tsx` - Key performance indicator displays
- `TopStatsBar.tsx` - Statistics summary bar

### Feature Components
Each major feature has its own directory with:
- Main component file
- Sub-components for specific functionality
- Type definitions
- Utility functions

### State Management
- React hooks for local state
- WebSocket connection for global real-time data
- No centralized state management (Redux/MobX)

## Development Workflow

1. **Install Dependencies**
   ```bash
   npm install          # Frontend
   cd api && npm install # Backend
   ```

2. **Start Development**
   ```bash
   npm run dev          # Frontend (Vite dev server)
   cd api && npm start  # WebSocket server
   ```

3. **Build Production**
   ```bash
   npm run build        # Creates dist/ directory
   ```

## Configuration

### Environment Variables
- `API_KEY` - For external API access
- `BITCOIN_RPC_*` - Bitcoin Core connection details
- `BRAIDPOOL_API_URL` - BraidPool simulator endpoint

### Ports
- Frontend Dev: 5173 (Vite default)
- WebSocket Server: 5000
- BraidPool Simulator: 65433

## Notable Implementation Details

1. **Real-Time Updates**: All data updates via WebSocket, no polling
2. **Type Safety**: Comprehensive TypeScript types for all data structures
3. **Responsive Design**: Mobile-friendly layouts using MUI breakpoints
4. **Dark Theme**: Consistent dark color scheme throughout
5. **Performance**: React.memo and useMemo for optimization
6. **Error Boundaries**: Graceful error handling in components