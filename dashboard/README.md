# Braidpool Dashboard

A visualization dashboard for the Braidpool decentralized mining pool, and Bitcoin related data.

## How to Run



### 🧩 Braid Visualization Setup Guide

To run the **Braid Visualization**, you have two options:

* Use the **deployed API**:

  ```
  http://french.braidpool.net:65433
  ```
* Or, run it **locally** via the `simulator_api` located in:

  ```
   tests/simulator_api.py
  ```

---

### ⚙️ Setup Instructions

1. Install dependencies
```
npm install
```
 2. Set environment variables
Use the example file as a reference: [`.env.example`](https://github.com/braidpool/braidpool/blob/dev/dashboard/api/.env.example)

# 3. Start the backend server
```
cd api
node server.js
```

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

## Features

- **Braid Visualization**: Interactive graph of the braid structure.
- **Performance Metrics**: Real-time mining pool statistics.
- **Miner Management**: Monitor and manage connected miners.
- **Network Analysis**: View network health and performance.




## Troubleshooting

- **Blank screen**: Check the browser console for errors.
- **Loading issues**: Verify that data files are in the correct format.
- **Visualization problems**: Ensure you are using a compatible browser (latest Chrome/Firefox recommended).
- **Visualization graph keeps on loading**: Ping the API, check the url of the API at dashboard/src/component/BraidPoolDAG/BraidPoolDAG.tsx.

---

For more details on the Braidpool project, visit the [main repository](https://github.com/braidpool/braidpool).
