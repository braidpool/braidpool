# Braidpool Dashboard

A visualization dashboard for the Braidpool decentralized mining pool.

## Quick Start

```bash
# Install dependencies
npm install

# Start development server
npm run dev
```

The dashboard will open automatically at [http://localhost:3000](http://localhost:3000).

## Build for Production

```bash
# Create optimized build
npm run build

# Preview production build locally
npm run preview
```

## Features

- **Braid Visualization**: Interactive graph of the braid structure.
- **Performance Metrics**: Real-time mining pool statistics.
- **Miner Management**: Monitor and manage connected miners.
- **Network Analysis**: View network health and performance.

## Dashboard Sections

1. **Main Dashboard**: Overview of key metrics and status.
2. **Braid Visualization**: Interactive graph showing the DAG structure.
3. **Mining Inventory**: Status of connected mining hardware.
4. **Statistics**: Detailed performance metrics and history.

## File Structure

The project is organized as follows:

```
dashboard/
├── .gitignore
├── favicon.ico
├── index.html
├── manifest.json
├── package.json
├── postcss.config.cjs
├── README.md
├── tailwind.config.js
├── tsconfig.json
├── tsconfig.node.json
├── vite.config.ts
├── assets/
│   ├── logo192.png
│   ├── logo512.png
├── public/
│   ├── favicon.ico
│   ├── logo192.png
│   ├── logo512.png
│   ├── manifest.json
│   ├── robots.txt
├── src/
│   ├── App.css
│   ├── App.test.tsx
│   ├── App.tsx
│   ├── env.d.ts
│   ├── index.css
│   ├── index.tsx
│   ├── logo.svg
│   ├── react-app-env.d.ts
│   ├── reportWebVitals.ts
│   ├── setupTests.ts
│   ├── components/
│   │   ├── BraidPoolDAG.tsx
│   │   ├── BraidStats.tsx
│   │   ├── Dashboard.tsx
│   │   ├── DashboardMetrics.tsx
│   │   ├── InstallationInstructions.tsx
│   │   ├── MinerDashboardComponents/
│   │   │   ├── Filters.tsx
│   │   │   ├── MinerChart.tsx
│   │   │   ├── MinerTable.tsx
│   │   │   ├── Particles.tsx
│   │   ├── common/
│   │   │   ├── Card.tsx
│   ├── data/
│   │   ├── mockBeads.ts
│   ├── theme/
│   │   ├── colors.ts
│   ├── types/
│   │   ├── Bead.ts
│   │   ├── braid.ts
│   ├── utils/
│       ├── braidDataTransformer.ts
```

## Dependencies

The project uses the following dependencies:

### Core Dependencies
- **React**: `^19.1.0` - For building the user interface.
- **React DOM**: `^19.1.0` - For rendering React components.
- **TypeScript**: `^5.8.3` - For type safety and development.
- **Vite**: `^6.2.6` - For fast development and build tooling.

### UI and Styling
- **Material UI**: `^7.0.1` - For prebuilt UI components.
- **Tailwind CSS**: `^4.1.3` - For utility-first CSS styling.

### Data Visualization
- **D3.js**: `^7.9.0` - For creating data-driven visualizations.

### Animations
- **Framer Motion**: `^12.6.5` - For animations and transitions.

### Utilities
- **Axios**: `^1.8.4` - For making HTTP requests.
- **Socket.IO Client**: `^4.8.1` - For real-time communication.

### Testing
- **Vitest**: `^3.1.1` - For unit testing.
- **Testing Library**: For DOM testing utilities.

## Development

This dashboard is built with:

- **React 19** with **TypeScript** for a modern, type-safe development experience.
- **Vite** for fast development and optimized builds.
- **Material UI** and **Tailwind CSS** for responsive and accessible UI components.
- **D3.js** for interactive data visualizations.

## Troubleshooting

- **Blank screen**: Check the browser console for errors.
- **Loading issues**: Verify that data files are in the correct format.
- **Visualization problems**: Ensure you are using a compatible browser (latest Chrome/Firefox recommended).

---

For more details on the Braidpool project, visit the [main repository](https://github.com/braidpool/braidpool).
