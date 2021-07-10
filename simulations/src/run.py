import logging
import random

import networkx as nx
import simpy

from config import config
from topology import Topology


def run():
    # Setup and start the simulation
    logging.basicConfig(format='%(levelname)s:%(message)s',
                        level=config['logging']['level'])

    logging.info('Process communication')
    random.seed(config['simulation']['random_seed'])
    env = simpy.Environment()

    network = Topology(env=env, num_nodes=3, num_neighbours=2)
    for node in network.nodes:
        node.start()

    logging.info('\nP2P broadcast communication\n')
    env.run(until=config['simulation']['run_time'])

    for node in network.nodes:
        logging.info(f'At {node.name}')
        logging.debug(list(nx.lexicographical_topological_sort(node.dag)))
        logging.debug(node.dag.edges())
        if config.getboolean('simulation', 'save_dot'):
            g = nx.nx_agraph.to_agraph(node.dag)
            g.layout()
            g.draw(f'/tmp/node_{node.name}.png', prog='dot')
        logging.info(node.shares_not_rewarded)


if __name__ == '__main__':
    run()
