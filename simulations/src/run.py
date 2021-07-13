import argparse
import logging
import random

import networkx as nx
import simpy

from config import config
from topology import Topology


def run(*, num_nodes, num_neighbours):
    # Setup and start the simulation
    logging.basicConfig(format='%(levelname)s:%(message)s',
                        level=config['logging']['level'])

    logging.info('Process communication')
    random.seed(config['simulation']['random_seed'])
    env = simpy.Environment()

    network = Topology(env=env, num_nodes=5, num_neighbours=4)
    for node in network.nodes.values():
        node.start()

    logging.info('\nP2P broadcast communication\n')
    env.run(until=config['simulation']['run_time'])

    for node in network.nodes.values():
        logging.info(f'At {node.name}')
        logging.debug(list(nx.lexicographical_topological_sort(node.dag)))
        logging.debug(node.dag.edges())
        if config.getboolean('simulation', 'save_dot'):
            g = nx.nx_agraph.to_agraph(node.dag)
            g.layout()
            g.draw(f'/tmp/node_{node.name}.png', prog='dot')
        logging.info(node.shares_not_rewarded)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--num_nodes', '-n', type=int, help='Number of nodes')
    parser.add_argument('--num_neighbours', '-d', type=int, help='Number of neighbors per node')
    args = parser.parse_args()
    run(num_nodes=args.num_nodes, num_neighbours=args.num_neighbours)
