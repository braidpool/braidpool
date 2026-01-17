# Braidpool Dashboard

The Braidpool Dashboard uses a modular, tab-based architecture.
Dashboard sections such as Dashboard, Braid Visualization, Bead Explorer, Mining Inventory, Bitcoin Stats, Mempool, and Node Health operate independently, each with its own configuration, API endpoints, and data flow.

---

## Running the Braid Visualization

To run the **Braid Visualization**, you have two options:

#### Option 1: Use the deployed API

```
http://french.braidpool.net:65433
```

#### Option 2: Run locally using the simulator API

The simulator is located at:

```
tests/simulator_api.py
```

---

## Running Other Dashboard Tabs

_(Bead Explorer, Bitcoin Stats, Mempool, Node Health)_

These tabs rely on the **dashboard backend API**.

#### 1. Start the Backend API

```bash
cd braidpool/dashboard/api
npm install
```

#### 2. Configure Environment Variables

Use the example file as reference:
[https://github.com/braidpool/braidpool/blob/dev/dashboard/api/.env.example](https://github.com/braidpool/braidpool/blob/dev/dashboard/api/.env.example)

#### 3. Run the Backend Server

```bash
node server.js
```

The API will be available at:
**[http://localhost:5000](http://localhost:5000)**

---

#### 4. Start the Frontend Dashboard

```bash
cd braidpool/dashboard
npm install
npm run dev
```

The dashboard will open at:
**[http://localhost:3000](http://localhost:3000)**

---

## Build for Production

```bash
# Create optimized build
npm run build

# Preview production build locally
npm run preview
```

---

## 🐳 Docker Setup

You can use **Docker Compose** to run the frontend, backend API, and simulator together.

#### Run All Services

```bash
docker-compose up --build
```

#### Services

- Frontend: [http://localhost:3000](http://localhost:3000)
- API: [http://localhost:5000](http://localhost:5000)
- Simulator API: [http://localhost:65433](http://localhost:65433)

#### Stop Services

```bash
docker-compose down
```

---

## Technology Stack

#### Frontend

- TypeScript 4.9+
- TailwindCSS 3.0+

### Backend

##### API Server

- Node.js
- Express.js
- WebSocket support

##### Mining Interface

- Python 3.7+
- Flask
- pyasic library

##### Development Tools

- Docker & Docker Compose
- ESLint & Prettier
- Jest & React Testing Library
- Python pytest

---

## Troubleshooting

- **Blank screen**: Check the browser console for errors.
- **Loading issues**: Verify API availability and response format.
- **Visualization issues**: Use the latest Chrome or Firefox.

If the issue persists, please open a GitHub issue with relevant logs and screenshots, or reach out on our
[Discord channel](https://discord.gg/pZYUDwkpPv).
The maintainers will review the report and help resolve or fix the issue.

---

For more information about the Braidpool project, see the
**[Braidpool main repository](https://github.com/braidpool/braidpool)**

---
