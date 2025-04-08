from flask import Flask
from flask_socketio import SocketIO
from flask_cors import CORS
import threading
import time
from simulator import Network
from braid import number_beads, reverse, descendant_work, highest_work_path, cohorts
import logging

logging.basicConfig(level=logging.INFO)

app = Flask(__name__)
CORS(app)
socketio = SocketIO(app, cors_allowed_origins="*", async_mode="threading")


class BraidSimulator:
    def __init__(self):
        self.network = Network(nnodes=50, target=2**240 - 1, hashrate=800000)
        self.current_beads = 0
        self.max_beads = 10000 
        self.bead_increment = 1 # increase or decrease for faster or slower simulation
        self.update_interval = 0.5

    def run(self):
        while self.current_beads < self.max_beads:
            new_beads = min(self.bead_increment, self.max_beads - self.current_beads)
            self.network.simulate(nbeads=new_beads, mine=False)
            self.current_beads += new_beads
            self.bead_increment = self.bead_increment + 1
            self.emit_braid_update()
            time.sleep(self.update_interval)

    def emit_braid_update(self):
        try:
            braid = self.network.nodes[0].braid
            hashed_parents = {
                int(k): list(map(int, v)) for k, v in dict(braid).items()
            }  # sets to lists (this is being done for easy parsing on frontend)
            parents = number_beads(hashed_parents)

            braid_data = {
                "highest_work_path": list(
                    map(str, highest_work_path(parents, reverse(parents)))
                ),
                "parents": {str(k): list(map(str, v)) for k, v in parents.items()},
                "children": {
                    str(k): list(map(str, v)) for k, v in reverse(parents).items()
                },
                "work": {str(k): v for k, v in descendant_work(parents).items()},
                "cohorts": [list(map(str, cohort)) for cohort in cohorts(parents)],
                "bead_count": len(braid.beads),
            }

            socketio.emit("braid_update", braid_data)
            print(braid_data)

        except Exception as e:
            logging.error(f"Error in emit_braid_update: {str(e)}", exc_info=True)
            raise


def start_simulator():
    simulator = BraidSimulator()
    simulator.run()


if __name__ == "__main__":
    threading.Thread(target=start_simulator, daemon=True).start()
    socketio.run(app, host="0.0.0.0", port=65433, debug=True)
