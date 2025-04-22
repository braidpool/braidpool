from flask import Flask, jsonify, render_template
from flask_socketio import SocketIO, emit
from flask_cors import CORS
import threading
import time
from simulator import Network
import braid
import logging

logging.basicConfig(level=logging.INFO)

app = Flask(__name__)
CORS(app)
socketio = SocketIO(app, cors_allowed_origins="*", async_mode="threading")

@socketio.on('connect')
def handle_connect():
    print('Client connected')
    emit('message', {'data': 'Connected to server'})

@socketio.on('disconnect')
def handle_disconnect():
    print('Client disconnected')

@socketio.on('message')
def handle_message(message):
    print(f'Received message: {message}')
    emit('message', {'data': f'Server received: {message}'})

class BraidSimulator:
    def __init__(self):
        self.network = Network(
            nnodes=25, target=2**240 - 1, hashrate=800000, target_algo="exp"
        )
        self.current_beads = 0
        self.bead_increment = 1
        self.update_interval = 0.5

    def run(self):
        while True:
            new_beads = self.bead_increment
            self.network.simulate(nbeads=new_beads, mine=False)
            self.current_beads += new_beads
            self.bead_increment += 1
            self.emit_braid_update()
            time.sleep(self.update_interval)

    def emit_braid_update(self):
        """ Emit the braid data for the last 10 cohorts. """
        try:
            braid0 = self.network.nodes[0].braid
            hashed_parents = {int(k): list(map(int, v)) for k, v in dict(braid0).items()}
            parents = hashed_parents
            bead_window = [b.hash for c in braid0.cohorts[-10:] for b in c]
            sub_parents = braid.sub_braid(bead_window, parents)
            sub_children = braid.reverse(sub_parents)

            braid_data = {
                "parents": {f"{int(k):064x}": list(map(lambda x: f"{int(x):064x}", v)) for k, v in sub_parents.items()},
                "cohorts": [[f"{int(b):064x}" for b in c] for c in braid0.cohorts[-10:]],
                "highest_work_path": list(f"{int(b):064x}" for b in braid.highest_work_path(sub_parents, sub_children))
            }

            socketio.emit("braid_update", braid_data)

        except Exception as e:
            logging.error(f"Error in emit_braid_update: {str(e)}", exc_info=True)
            # Don't raise the exception to prevent thread termination
            pass


def start_simulator():
    simulator = BraidSimulator()
    simulator.run()

if __name__ == "__main__":
    # Start the simulator in a background thread
    simulator_thread = threading.Thread(target=start_simulator, daemon=True)
    simulator_thread.start()

    # Run the Socket.IO server
    print("Starting Socket.IO server on http://0.0.0.0:65433")
    socketio.run(app, host="0.0.0.0", port=65433, debug=False, allow_unsafe_werkzeug=True)
