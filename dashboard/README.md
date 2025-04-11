# Braidpool Dashboard

A visualization dashboard for the Braidpool decentralized mining pool.

## Quick Start

```bash
# Install dependencies
npm install

# Start development server
npm run dev
```

The dashboard will open automatically at http://localhost:3000

## Build for Production

```bash
# Create optimized build
npm run build

# Preview production build locally
npm run preview
```

## Features

- **Braid Visualization**: Interactive graph of the braid structure
- **Performance Metrics**: Real-time mining pool statistics
- **Miner Management**: Monitor and manage connected miners
- **Network Analysis**: View network health and performance

## Dashboard Sections

1. **Main Dashboard**: Overview of key metrics and status
2. **Braid Visualization**: Interactive graph showing the DAG structure
3. **Mining Inventory**: Status of connected mining hardware
4. **Statistics**: Detailed performance metrics and history

## Data Structure

The dashboard visualizes braid data with the following structure:

- **Nodes**: Individual beads/shares in the braid
- **Links**: Connections between beads (parent-child relationships)
- **Cohorts**: Groups of beads organized by mining time/relationship

## Development

This dashboard is built with:

- React 19 with TypeScript
- Vite for fast development and building
- Material UI for components
- D3.js for data visualization

## Troubleshooting

- **Blank screen**: Check browser console for errors
- **Loading issues**: Verify data files are in the correct format
- **Visualization problems**: Check browser compatibility (latest Chrome/Firefox recommended)

---

For more details on the Braidpool project, visit the [main repository](https://github.com/braidpool/braidpool).
