# Braidpool Dashboard

A visualization dashboard for the Braidpool decentralized mining pool, and Bitcoin related data.

## How to Run

First and foremost, for the braid visualisation to work, either use the deployed API url http://french.braidpool.net:65433, or run it locally via the `simulator_api` located in the `tests` directory in the `main` directory.

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

## Troubleshooting

- **Blank screen**: Check the browser console for errors.
- **Loading issues**: Verify that data files are in the correct format.
- **Visualization problems**: Ensure you are using a compatible browser (latest Chrome/Firefox recommended).
- **Visualization graph keeps on loading**: Ping the API, check the url of the API at dashboard/src/component/BraidPoolDAG/BraidPoolDAG.tsx.

---

For more details on the Braidpool project, visit the [main repository](https://github.com/braidpool/braidpool).
