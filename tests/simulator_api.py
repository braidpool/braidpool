import asyncio
import json
import logging
import websockets
from simulator import Network
import braid

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Set of all connected websocket clients
connected_clients = set()

class BraidSimulator:
    def __init__(self):
        self.network = Network(
            nnodes=25, target=2**240 - 1, hashrate=800000, target_algo="exp"
        )
        self.current_beads = 0
        self.update_interval = 0.5 # 500ms update interval
        self.clients = set()

    async def run(self):
        while True:
            self.current_beads += 1
            self.network.simulate(nbeads=self.current_beads, mine=False)
            await self.broadcast_braid_update()
            await asyncio.sleep(self.update_interval)

    async def broadcast_braid_update(self):
        """ Broadcast the braid data for the last 10 cohorts to all connected clients. """
        try:
            braid0 = self.network.nodes[0].braid
            hashed_parents = {int(k): list(map(int, v)) for k, v in dict(braid0).items()}
            parents = hashed_parents

            # Get beads from the last 10 cohorts
            cohorts = braid0.cohorts[-10:] if len(braid0.cohorts) >= 10 else braid0.cohorts
            bead_window = [b.hash for c in cohorts for b in c]

            sub_parents = braid.sub_braid(bead_window, parents)
            sub_children = braid.reverse(sub_parents)

            braid_data = {
                "type": "braid_update",
                "data": {
                    "parents": {f"{int(k):064x}": list(map(lambda x: f"{int(x):064x}", v)) for k, v in sub_parents.items()},
                    "cohorts": [[f"{int(b):064x}" for b in c] for c in cohorts],
                    "highest_work_path": list(f"{int(b):064x}" for b in braid.highest_work_path(sub_parents, sub_children))
                }
            }

            # Convert to JSON and broadcast to all clients
            message = json.dumps(braid_data)

            # Create a copy of the set to avoid "set changed size during iteration" errors
            clients_copy = connected_clients.copy()

            for client in clients_copy:
                try:
                    await client.send(message)
                except websockets.exceptions.ConnectionClosed:
                    pass # Client is already disconnected, will be removed in the handler
                except Exception as e:
                    logger.error(f"Error sending to client: {e}")

        except Exception as e:
            logger.error(f"Error in broadcast_braid_update: {str(e)}", exc_info=True)
            # Don't raise the exception to prevent task termination

async def websocket_handler(websocket):
    """Handle a WebSocket connection from a client."""

    # Register the client
    connected_clients.add(websocket)
    logger.info(f"Client connected: {websocket.remote_address}")

    try:
        # Send welcome message
        await websocket.send(json.dumps({
            "type": "message",
            "data": "Connected to braid simulator"
        }))

        # Keep connection alive
        while True:
            try:
                message = await asyncio.wait_for(websocket.recv(), timeout=30)

                try:
                    data = json.loads(message)
                    logger.debug(f"Received message: {data}")

                except json.JSONDecodeError:
                    logger.warning(f"Received invalid JSON: {message}")
                    await websocket.send(json.dumps({
                        "type": "error",
                        "data": "Invalid JSON received"
                    }))

            # Send ping to keep connection alive
            except asyncio.TimeoutError:
                try:
                    await websocket.ping()
                except ConnectionError:
                    break

    except websockets.exceptions.ConnectionClosed as e:
        logger.info(f"Connection closed: {e.code} - {e.reason}")
    except Exception as e:
        logger.error(f"WebSocket error: {str(e)}", exc_info=True)
    finally:
        # Unregister the client
        connected_clients.discard(websocket)

async def main():
    # Create and start the simulator
    simulator = BraidSimulator()

    # Server configuration
    host = "0.0.0.0"
    port = 65433

    # Create and start the server
    async with websockets.serve(
        websocket_handler,
        host,
        port,
        ping_interval=20,
        ping_timeout=30,
        max_size=2**20  # 1MB max message size
    ) as server:
        await simulator.run() # Runs forever

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Server stopped by user")
    finally:
        logger.info("Server shutdown complete")
