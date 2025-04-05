# Braidpool Dashboard

A visualization and analytics dashboard for exploring and understanding the structure of the Braidpool mining pool's braid data.

![Braidpool Dashboard](./docs/dashboard-preview.png)

## 🚀 Quick Start

```bash
# Navigate to the dashboard directory
cd dashboard

# Install dependencies
npm install

# Start the development server
npm start
```

The application will be available at [http://localhost:3000](http://localhost:3000).

## 📋 Overview

This dashboard provides a visualization and analysis interface for braid data from the Braidpool mining pool. It helps users understand the structure of the mining pool's operation through visual representation and statistical analysis.

## ✨ Features

- **Interactive Braid Visualization**: Visualize the directed acyclic graph (DAG) structure of the braid with color-coded cohorts
- **Statistical Analysis**: View key metrics and derived statistics about the braid structure
- **Summary Dashboard**: Get a quick overview of the most important braid metrics
- **Tabbed Interface**: Navigate between different views of the data

## 🛠️ Tech Stack

- **React**: UI library
- **TypeScript**: Type safety
- **Material-UI**: Component library
- **D3.js**: Data visualization
- **React Router**: Navigation

## 📁 Project Structure

```
dashboard/
├── public/                 # Static files
├── src/                    # Source code
│   ├── components/         # React components
│   │   ├── BraidStats.tsx          # Statistics panel
│   │   └── BraidVisualization.tsx  # D3 visualization
│   ├── data/               # Sample data files
│   ├── pages/              # Page components
│   │   └── Dashboard.tsx   # Main dashboard page
│   ├── types/              # TypeScript types
│   │   └── braid.ts        # Braid data interfaces
│   ├── utils/              # Utility functions
│   │   └── braidDataTransformer.ts # Data transformation utilities
│   ├── App.tsx             # Application root
│   └── index.tsx           # Entry point
└── package.json            # Dependencies and scripts
```

## 📊 Data Structure

The dashboard works with data in the following structure:

```typescript
interface BraidVisualizationData {
  nodes: BraidNode[];       // Nodes in the graph
  links: BraidLink[];       // Connections between nodes
  cohorts: number[][];      # Cohort groupings
}
```

## 🔧 Development Notes

### Common Issues

1. **Material-UI Grid TypeScript Errors**  
   The dashboard uses Box components with flexbox styling instead of Grid components for layouts to avoid TypeScript errors with the Grid component's `item` prop.

2. **Data Transformation**  
   Raw braid data needs to be processed through the `transformBraidData` utility before visualization.

### Running a Production Build

```bash
npm run build
```

This creates an optimized production build in the `build` folder.

## 🔮 Future Enhancements

- **Live Data Integration**: Connect to real-time braid data from the mining pool
- **Additional Visualization Types**: Add alternative views like heatmaps and time-series
- **Performance Optimizations**: Enhance rendering performance for large braids
- **User Controls**: Add filters and controls for interacting with the visualization
- **Export Options**: Allow export of visualization and statistics

## 🤝 Contributing

1. Make sure to run the development server from the `dashboard` directory
2. When making changes to the visualization, check for both visual correctness and statistical accuracy
3. Test with different data structures to ensure robustness

## 📝 License

[Add appropriate license here]

---

Created for the Braidpool project - A decentralized mining pool implementation.
