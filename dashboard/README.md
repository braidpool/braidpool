# Braidpool Dashboard

A visualization dashboard for the Braidpool decentralized mining pool, and Bitcoin related data.

## How to Run

### 🧩 Braid Visualization Setup Guide

To run the **Braid Visualization**, you have two options:

- Use the **deployed API**:

  ```
  http://french.braidpool.net:65433
  ```

- Or, run it **locally** via the `simulator_api` located in:

  ```
   tests/simulator_api.py
  ```

---

### ⚙️ Setup Instructions

1. Install dependencies

```
npm install
```

2.  Set environment variables
    Use the example file as a reference: [`.env.example`](https://github.com/braidpool/braidpool/blob/dev/dashboard/api/.env.example)

# 3. Start the backend server

```
cd api
node server.js
```

The server will run at http://localhost:5000

# 4. Start the frontend development server

```
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

## 🐳 Docker Setup

You can use **Docker Compose** to spin up all required services- the frontend, backend API, and simulator with a single command.

Run All Services

```bash
Build and start all containers

docker-compose up --build
```

Once running:

Frontend: http://localhost:3000

API: http://localhost:5000

Simulator API: http://localhost:65433

To Stop Containers

```
docker-compose down
```

## Technology Stack

### Frontend

- **Core**
  - React 18+
  - TypeScript 4.9+
  - Vite (Build tooling)
  - TailwindCSS 3.0+

- **Data Visualization**
  - D3.js (Braid visualization)
  - React Charts
  - Custom graph components

- **State Management**
  - React Context API
  - Custom hooks
  - Real-time data handling

### Backend

- **API Server**
  - Node.js
  - Express.js
  - WebSocket support
  - RESTful endpoints

- **Mining Interface**
  - Python 3.7+
  - Flask
  - pyasic library
  - WebSocket server

- **Development Tools**
  - Docker & Docker Compose
  - ESLint & Prettier
  - Jest & React Testing Library
  - Python pytest

## Features

- **Braid Visualization**: Interactive graph of the braid structure.
- **Performance Metrics**: Real-time mining pool statistics.
- **[Miner Inventory Dashboard](./MinerInventory.md)**: Comprehensive system for monitoring and managing ASIC miners.
  - Real-time monitoring of multiple miners
  - Device health tracking
  - Performance metrics and alerts
  - Pool configuration monitoring
- **Network Analysis**: View network health and performance.

## Troubleshooting

- **Blank screen**: Check the browser console for errors.
- **Loading issues**: Verify that data files are in the correct format.
- **Visualization problems**: Ensure you are using a compatible browser (latest Chrome/Firefox recommended).
- **Visualization graph keeps on loading**: Ping the API, check the url of the API at dashboard/src/component/BraidPoolDAG/BraidPoolDAG.tsx.

---

For more details on the Braidpool project, visit the [main repository](https://github.com/braidpool/braidpool).
