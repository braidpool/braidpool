from flask import Flask, jsonify
from flask_socketio import SocketIO
from flask_cors import CORS
from flasgger import Swagger, swag_from
import threading
import time
from simulator import Network
from braid import reverse, descendant_work, highest_work_path, cohorts
import logging

logging.basicConfig(level=logging.INFO)

app = Flask(__name__)
CORS(app)
socketio = SocketIO(app, cors_allowed_origins="*", async_mode="threading")

swagger = Swagger(app)

@app.route("/hello")
@swag_from({
    'responses': {
        200: {
            'description': 'Returns a simple hello message',
            'examples': {
                'text': 'Hello Braidpool'
            }
        }
    }
})
def hello():
    return "Hello Braidpool"

braid_data = {}

@app.route("/test_data")
@swag_from({
    'responses': {
        200: {
            'description': 'Returns simulated braid data',
            'schema': {
                'type': 'object',
                'properties': {
                    'highest_work_path': {
                        'type': 'array',
                        'items': {'type': 'string'}
                    },
                    'parents': {'type': 'object'},
                    'children': {'type': 'object'},
                    'work': {'type': 'object'},
                    'cohorts': {
                        'type': 'array',
                        'items': {
                            'type': 'array',
                            'items': {'type': 'string'}
                        }
                    },
                    'bead_count': {'type': 'integer'}
                }
            }
        }
    }
})
def data():
    logging.info(f"Returning braid_data on test_data endpoint")
    return jsonify(braid_data)


class BraidSimulator:
    def __init__(self):
        self.network = Network(
            nnodes=50, target=2**240 - 1, hashrate=800000, target_algo="exp"
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
        global braid_data
        try:
            braid = self.network.nodes[0].braid
            hashed_parents = {
                int(k): list(map(int, v)) for k, v in dict(braid).items()
            }
            parents = hashed_parents

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
            logging.log(braid_data["bead_count"])

        except Exception as e:
            logging.error(f"Error in emit_braid_update: {str(e)}", exc_info=True)
            raise


def start_simulator():
    simulator = BraidSimulator()
    simulator.run()


if __name__ == "__main__":
    threading.Thread(target=start_simulator, daemon=True).start()
    socketio.run(app, host="0.0.0.0", port=65433, debug=True)
